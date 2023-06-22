/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use ast::{EntityUID, Name, RestrictedExpr, StaticPolicy};
use cedar_policy_core::ast::{self, Value};
use crate::collections::HashMap;
use crate::err::{while_doing, Error, Result};
use crate::{accum, gen, gen_inner, uniform};
use crate::policy::GeneratedPolicy;
use crate::request::Request;
use crate::size_hint_utils::size_hint_for_choose;
use arbitrary::{Arbitrary, Unstructured};
use smol_str::SmolStr;
use std::cell::RefCell;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::ops::{Deref, DerefMut};

const MAX_PATTERN_LEN: usize = 6;

/// Settings controlling the generation of ABAC hierarchies/policies/requests
#[derive(Debug, Clone)]
pub struct ABACSettings {
    /// If true, generates well-typed hierarchies/policies/requests.
    /// Specifically:
    /// - policies will not throw type errors, ie, we generate subexpressions of the proper type for ops like < or .contains()
    /// - attribute values (in the hierarchy and in the request contexts) will strictly adhere to the types suggested in pool.ty_data
    ///
    /// If false, does not attempt to match types.
    pub match_types: bool,
    /// If true, may generate extension function calls in policies and/or
    /// attribute values.
    pub enable_extensions: bool,
    /// Maximum depth of an expression or type. E.g., maximum nesting of sets.
    ///
    /// This is used in the following places:
    /// - Maximum depth of the expression in a when/unless clause
    ///     - Note that this is only the limit for _each_ `when` and `unless`
    ///     clause.
    ///     Some generated policies will have multiple `when` and `unless`
    ///     clauses, in which case the conjunction of all conditions may exceed
    ///     the `max_depth`. But, the `max_depth` still applies for each clause
    ///     individually.
    /// - Maximum depth of expressions in attribute values in the hierarchy,
    ///     and also of attributes of `context` in each request
    /// - Maximum depth of a type specified in a generated schema
    /// - Maximum number of when/unless clauses in a policy
    pub max_depth: usize,
    /// Maximum width of an expression or type. E.g., maximum number of elements
    /// in a set.
    ///
    /// This is used in the following places:
    /// - Maximum number of elements in a set in an attribute value in the
    ///     hierarchy
    /// - Maximum number of elements in a set literal in a policy
    /// - Maximum number of attributes in a record in an attribute value in the
    ///     hierarchy
    /// - Maximum number of attributes in a record literal in a policy
    /// - Maximum number of UIDs in the hierarchy of any given entity type
    /// - Maximum number of "additional attributes" on any entity in the
    ///     hierarchy
    pub max_width: usize,
    /// Whether to enable the `additional_attributes` flag in generated schemas.
    /// If this option is `false`, `additional_attributes` will always be false
    /// in all generated schemas.
    /// If this option is `true`, `additional_attributes` will be randomly
    /// chosen to be either true or false every time it appears.
    /// Generated attribute data also respects the value of
    /// `additional_attributes` in the schema: it may add additional attributes,
    /// but only if `additional_attributes` is true.
    pub enable_additional_attributes: bool,
    /// Flag to globally enable/disable generation of expressions containing the
    /// `like` operator.
    pub enable_like: bool,
    /// Flag to enable/disable generating actions in groups and declaring
    /// attributes on entity types.
    pub enable_action_groups_and_attrs: bool,
    /// Flag to enable/disable generating arbitrary extension function calls.
    /// Note that this flag is only considered if `enable_extensions` is true.
    /// This flag should only be disabled for target `pp` because the parser now
    /// rejects unknown extension function calls.
    pub enable_arbitrary_func_call: bool,

    /// Flag to enable/disable generating unknowns, exercising partial evaluation
    pub enable_unknowns: bool,
}

// Mutate a hypothetically valid string (randomly).
// We want to the make the probability of keeping the valid input reasonable:
// We try to mutate each character with a small probability p because the
// probability where the whole string is unaffected is expotential to 1-p.
// The mutation consists of deletion, duplication, and randomization.
fn mutate_str(u: &mut Unstructured<'_>, s: &str) -> Result<String> {
    let mut res = Vec::new();
    for c in s.chars() {
        if u.ratio(9, 10)? {
            res.push(c);
        } else {
            gen!(u,
                1 =>
                    // remove it
                    {},
                1 =>
                // duplicate it
                {
                    res.push(c);
                    res.push(c);
                },
                2 =>
                // replace it with an arbitrary ASCII
                {
                    let byte = u.bytes(1)?.first().unwrap().to_owned();
                    res.push(byte as char);
                },
                4 =>
                // keep it
                {
                    res.push(c);
                }
            )
        }
    }
    Ok(res.into_iter().collect())
}

/// Pool of "unknowns"
#[derive(Debug, Clone, Default)]
pub struct UnknownPool {
    unknowns: RefCell<HashMap<String, (Type, Value)>>,
}

impl UnknownPool {
    /// Given the name of an unknown, get its `Type`, or `None` if it's not in
    /// the pool
    pub fn get_type(&self, unk: impl AsRef<str>) -> Option<Type> {
        self.unknowns
            .borrow()
            .get(unk.as_ref())
            .map(|(t, _)| t)
            .cloned()
    }

    /// Iterate over the unknowns in the pool, getting the name of the unknown
    /// and its `Type`
    pub fn unknowns(self) -> impl Iterator<Item = (String, Type)> {
        self.unknowns.take().into_iter().map(|(k, (t, _))| (k, t))
    }

    /// Iterate over the unknowns in the pool, getting the name of the unknown
    /// and its `Value`
    pub fn mapping(self) -> impl Iterator<Item = (String, Value)> {
        self.unknowns.take().into_iter().map(|(k, (_, v))| (k, v))
    }

    /// Create a new unknown with the given `Type` and `Value`. Returns the new
    /// name as a `String`
    pub fn alloc(
        &self,
        t: Type,
        v: Value,
    ) -> String {
        let this = format!("{}", self.unknowns.borrow().len());
        self.unknowns.borrow_mut().insert(this.clone(), (t, v));
        this
    }
}

/// Pool of integer and string constants
#[derive(Debug, Clone)]
pub struct ConstantPool {
    /// integer constants to choose from. we generate a finite list as part of
    /// the pool in order to increase the chance of integers actually being
    /// equal (eg, two attributes having equal values, or an attribute value
    /// being equal to a constant mentioned in the policy)
    int_constants: Vec<i64>,
    /// string constants to choose from. we generate a finite list as part of
    /// the pool in order to increase the chance of strings actually being
    /// equal (eg, two attributes having equal values, or an attribute value
    /// being equal to a constant mentioned in the policy)
    string_constants: Vec<SmolStr>,
}

impl<'a> Arbitrary<'a> for ConstantPool {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let sc: Vec<String> = u.arbitrary()?;
        Ok(Self {
            int_constants: u.arbitrary()?,
            string_constants: sc.iter().map(|s| s.into()).collect(),
        })
    }
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            <Vec<i64> as Arbitrary>::size_hint(depth),
            <Vec<String> as Arbitrary>::size_hint(depth),
        ])
    }
}

impl ConstantPool {
    /// Get an arbitrary int constant from the pool.
    /// If there are no int constants in the pool, get a purely arbitrary int constant
    pub fn arbitrary_int_constant(&self, u: &mut Unstructured<'_>) -> Result<i64> {
        u.choose(&self.int_constants).copied().or_else(|_| {
            u.arbitrary()
                .map_err(|e| while_doing("getting an arbitrary int constant", e))
        })
    }

    /// size hint for arbitrary_int_constant()
    pub fn arbitrary_int_constant_size_hint(_depth: usize) -> (usize, Option<usize>) {
        size_hint_for_choose(None)
    }

    /// Get an arbitrary string constant from the pool, with maximum size
    /// indicated by `bound`. If there are no string constants in the pool,
    /// get a purely arbitrary string constant with that maximum size
    pub fn arbitrary_string_constant_bounded(
        &self,
        u: &mut Unstructured<'_>,
        bound: usize,
    ) -> Result<SmolStr> {
        let short_consts: Vec<&SmolStr> = self
            .string_constants
            .iter()
            .filter(|s| s.len() < bound)
            .collect();
        u.choose(&short_consts)
            .map(|s| (*s).clone())
            .map_err(|e| while_doing("Getting an arbitrary string constant", e))
            .or_else(|_| arbitrary_string(u, Some(bound)))
    }

    /// Get an arbitrary string constant from the pool.
    /// If there are no string constants in the pool, get a purely arbitrary string constant
    pub fn arbitrary_string_constant(&self, u: &mut Unstructured<'_>) -> Result<SmolStr> {
        u.choose(&self.string_constants).cloned().or_else(|_| {
            u.arbitrary::<String>()
                .map(|s| s.into())
                .map_err(|e| while_doing("getting an arbitrary string constant", e))
        })
    }

    /// Produce a RHS of a like operation
    /// It's derived from a random string constant in the pool: We perform transformations over it such as adding a char, deleting a char and adding a wildcard star.
    pub fn arbitrary_pattern_literal(
        &self,
        u: &mut Unstructured<'_>,
    ) -> Result<Vec<ast::PatternElem>> {
        let matched_string = self.arbitrary_string_constant_bounded(u, MAX_PATTERN_LEN)?;

        let mut pattern = Vec::new();
        for c in matched_string.chars() {
            uniform!(
                u,
                // add the char back
                {
                    pattern.push(ast::PatternElem::Char(c));
                },
                // add the wildcard
                {
                    pattern.push(ast::PatternElem::Wildcard);
                },
                // add the wildcard after the char
                {
                    pattern.push(ast::PatternElem::Char(c));
                    pattern.push(ast::PatternElem::Wildcard);
                },
                // add the wildcard before the char
                {
                    pattern.push(ast::PatternElem::Wildcard);
                    pattern.push(ast::PatternElem::Char(c));
                },
                // Skip
                {}
            )
        }
        Ok(pattern)
    }

    // Generate a valid IPv4 net representation
    fn arbitrary_ipv4_str(&self, u: &mut Unstructured<'_>) -> Result<String> {
        let bytes: [u8; 4] = u.bytes(4)?.try_into().unwrap();
        let ip = Ipv4Addr::from(bytes);
        // Produce a CIDR notation out of 50% probability
        Ok(if u.ratio(1, 2)? {
            ip.to_string()
        } else {
            // We could construct a `IPv4Net` here but that implies an additional dependency
            let prefix = u.int_in_range(0..=32)?;
            format!("{}/{}", ip, prefix)
        })
    }

    // Generate a valid IPv6 net representation
    fn arbitrary_ipv6_str(&self, u: &mut Unstructured<'_>) -> Result<String> {
        let bytes: [u8; 16] = u.bytes(16)?.try_into().unwrap();
        let ip = Ipv6Addr::from(bytes);
        // Produce a CIDR notation out of a 50% probability
        Ok(if u.ratio(1, 2)? {
            ip.to_string()
        } else {
            // We could construct a `IPv4Net` here but that implies an additional dependency
            let prefix = u.int_in_range(0..=128)?;
            format!("{}/{}", ip, prefix)
        })
    }

    /// Generate a valid IP net representation and mutate it
    pub fn arbitrary_ip_str(&self, u: &mut Unstructured<'_>) -> Result<SmolStr> {
        let valid_str = if u.ratio(1, 2)? {
            self.arbitrary_ipv4_str(u)?
        } else {
            self.arbitrary_ipv6_str(u)?
        };
        mutate_str(u, &valid_str).map(SmolStr::new)
    }

    /// Generate a valid decimal number representation and mutate it
    pub fn arbitrary_decimal_str(&self, u: &mut Unstructured<'_>) -> Result<SmolStr> {
        let bytes = u.bytes(8)?;
        let i = i64::from_be_bytes(bytes.try_into().unwrap());
        mutate_str(
            u,
            // Replicate from Core
            &format!("{}.{}", i / i64::pow(10, 4), (i % i64::pow(10, 4)).abs()),
        )
        .map(SmolStr::new)
    }

    /// size hint for arbitrary_string_constant()
    pub fn arbitrary_string_constant_size_hint(_depth: usize) -> (usize, Option<usize>) {
        size_hint_for_choose(None)
    }
}

/// Generate an arbitrary string of up to `bound` size
fn arbitrary_string(
    u: &mut Unstructured<'_>,
    bound: Option<usize>,
) -> Result<SmolStr> {
    let s: String = u.arbitrary()?;
    let result_s = if let Some(bound) = bound {
        if s.len() < bound {
            SmolStr::from(s)
        } else {
            s.chars().take(bound).collect()
        }
    } else {
        s.into()
    };
    Ok(result_s)
}

/// Data describing an extension function available for use in policies/etc
#[derive(Debug, Clone)]
pub struct AvailableExtensionFunction {
    /// Name of the extension function
    pub name: Name,
    /// Is it considered a constructor (ie, is it legal as an attribute value).
    /// All constructors must have return types that are extension values.
    pub is_constructor: bool,
    /// Parameter types expected by the extension function. The length of this
    /// list indicates the function arity.
    pub parameter_types: Vec<Type>,
    /// Return type of the extension function
    pub return_ty: Type,
}

/// Struct holding information about all available extension functions
#[derive(Debug, Clone)]
pub struct AvailableExtensionFunctions {
    /// available extension functions (constructors only).
    /// Empty if settings.enable_extensions is false
    constructors: Vec<AvailableExtensionFunction>,
    /// available extension functions (all functions).
    /// Empty if settings.enable_extensions is false
    all: Vec<AvailableExtensionFunction>,
    /// available constructors, by their return types (map keys are return types).
    /// Empty if settings.enable_extensions is false and/or settings.match_types is false
    constructors_by_type: HashMap<Type, Vec<AvailableExtensionFunction>>,
    /// available extension functions, by their return types (map keys are return types).
    /// Empty if settings.enable_extensions is false and/or settings.match_types is false
    all_by_type: HashMap<Type, Vec<AvailableExtensionFunction>>,
}

impl AvailableExtensionFunctions {
    /// Create a new `AvailableExtensionFunctions` object based on the given `settings`
    pub fn create(settings: &ABACSettings) -> Self {
        let available_ext_funcs = if settings.enable_extensions {
            vec![
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("ip").expect("should be a valid identifier"),
                    is_constructor: true,
                    parameter_types: vec![Type::string()],
                    return_ty: Type::ipaddr(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("isIpv4")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::ipaddr()],
                    return_ty: Type::bool(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("isIpv6")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::ipaddr()],
                    return_ty: Type::bool(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("isLoopback")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::ipaddr()],
                    return_ty: Type::bool(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("isMulticast")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::ipaddr()],
                    return_ty: Type::bool(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("isInRange")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::ipaddr(), Type::ipaddr()],
                    return_ty: Type::bool(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("decimal")
                        .expect("should be a valid identifier"),
                    is_constructor: true,
                    parameter_types: vec![Type::string()],
                    return_ty: Type::decimal(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("lessThan")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::decimal(), Type::decimal()],
                    return_ty: Type::bool(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("lessThanOrEqual")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::decimal(), Type::decimal()],
                    return_ty: Type::bool(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("greaterThan")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::decimal(), Type::decimal()],
                    return_ty: Type::bool(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("greaterThanOrEqual")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::decimal(), Type::decimal()],
                    return_ty: Type::bool(),
                },
            ]
        } else {
            vec![]
        };
        let constructors = available_ext_funcs
            .iter()
            .filter(|func| func.is_constructor)
            .cloned()
            .collect::<Vec<_>>();
        let mut constructors_by_type: HashMap<Type, Vec<AvailableExtensionFunction>> =
            HashMap::new();
        if settings.match_types {
            for func in &constructors {
                constructors_by_type
                    .entry(func.return_ty.clone())
                    .or_default()
                    .push(func.clone());
            }
        }
        let mut all_by_type: HashMap<Type, Vec<AvailableExtensionFunction>> = HashMap::new();
        if settings.match_types {
            for func in &available_ext_funcs {
                all_by_type
                    .entry(func.return_ty.clone())
                    .or_default()
                    .push(func.clone());
            }
        }
        Self {
            constructors,
            all: available_ext_funcs,
            constructors_by_type,
            all_by_type,
        }
    }

    /// Get any extension constructor
    pub fn arbitrary_constructor<'s>(
        &'s self,
        u: &mut Unstructured<'_>,
    ) -> Result<&'s AvailableExtensionFunction> {
        u.choose(&self.constructors)
            .map_err(|e| while_doing("getting arbitrary extfunc constructor", e))
    }
    /// size hint for `arbitrary_constructor()`
    pub fn arbitrary_constructor_size_hint(_depth: usize) -> (usize, Option<usize>) {
        size_hint_for_choose(Some(3))
    }

    /// Get any extension function
    pub fn arbitrary_all<'s>(
        &'s self,
        u: &mut Unstructured<'_>,
    ) -> Result<&'s AvailableExtensionFunction> {
        u.choose(&self.all)
            .map_err(|e| while_doing("getting arbitrary extfunc", e))
    }
    /// size hint for `arbitrary_all()`
    pub fn arbitrary_all_size_hint(_depth: usize) -> (usize, Option<usize>) {
        size_hint_for_choose(Some(8))
    }

    /// Get an extension constructor that returns the given type
    pub fn arbitrary_constructor_for_type<'a, 'u>(
        &'a self,
        ty: &Type,
        u: &mut Unstructured<'u>,
    ) -> Result<&'a AvailableExtensionFunction> {
        let choices: &'a [AvailableExtensionFunction] =
            self.constructors_by_type
                .get(ty)
                .ok_or(Error::EmptyChoose {
                    doing_what: "getting extfunc constructors for given type",
                })?;
        u.choose(choices)
            .map_err(|e| while_doing("getting arbitrary extfunc constructor with given type", e))
    }

    /// size hint for arbitrary_constructor_for_type()
    pub fn arbitrary_constructor_for_type_size_hint(_depth: usize) -> (usize, Option<usize>) {
        size_hint_for_choose(Some(3))
    }

    /// Get an extension function that returns the given type
    pub fn arbitrary_for_type<'a, 'u>(
        &'a self,
        ty: &Type,
        u: &mut Unstructured<'u>,
    ) -> Result<&'a AvailableExtensionFunction> {
        let choices: &'a [AvailableExtensionFunction] =
            self.all_by_type.get(ty).ok_or(Error::EmptyChoose {
                doing_what: "getting arbitrary extfunc with given return type",
            })?;
        u.choose(choices)
            .map_err(|e| while_doing("getting arbitrary extfunc with given type", e))
    }

    /// size hint for arbitrary_for_type()
    pub fn arbitrary_for_type_size_hint(_depth: usize) -> (usize, Option<usize>) {
        size_hint_for_choose(Some(8))
    }
}

/// Approximation of the Cedar type system used by the type-directed
/// generator
#[derive(Debug, Clone, PartialEq, Eq, Hash, Arbitrary)]
pub enum Type {
    /// Bool
    Bool,
    /// Long (integer)
    Long,
    /// String
    String,
    /// Set, with the given element type. Note that we only generate
    /// homogeneous sets.
    /// Set(None) means any set type. It will still be a homogeneous set.
    Set(Option<Box<Type>>),
    /// Note that for now we have only a single Record type: all records are the
    /// same type, no effort to generate records with particular attributes
    Record,
    /// Note that for now we have only a single Entity type: all entities are
    /// the same type, no effort to generate entities with particular
    /// attributes, or distinguish entities of different entity types
    Entity,
    /// IP address
    IPAddr,
    /// Decimal numbers
    Decimal,
}

impl Type {
    /// Bool type
    pub fn bool() -> Self {
        Type::Bool
    }
    /// Long type
    pub fn long() -> Self {
        Type::Long
    }
    /// String type
    pub fn string() -> Self {
        Type::String
    }
    /// Set type, with the given element type
    pub fn set_of(element_ty: Type) -> Self {
        Type::Set(Some(Box::new(element_ty)))
    }
    /// Set type, without specifying the element type. (It will still be a
    /// homogeneous set.)
    pub fn any_set() -> Self {
        Type::Set(None)
    }
    /// Record type
    pub fn record() -> Self {
        Type::Record
    }
    /// Entity type
    pub fn entity() -> Self {
        Type::Entity
    }
    /// IP type
    pub fn ipaddr() -> Self {
        Type::IPAddr
    }
    /// Decimal type
    pub fn decimal() -> Self {
        Type::Decimal
    }

    /// `Type` has `Arbitrary` auto-derived for it, but for the case where you
    /// want "any nonextension Type", you have this
    pub fn arbitrary_nonextension(u: &mut Unstructured<'_>) -> Result<Type> {
        Ok(uniform!(
            u,
            Type::bool(),
            Type::long(),
            Type::string(),
            Type::set_of(Self::arbitrary_nonextension(u)?),
            Type::any_set(),
            Type::record(),
            Type::entity()
        ))
    }
}

/// attribute values are restricted expressions: just
/// - bool literals
/// - int literals
/// - string literals
/// - UID literals
/// - extension function calls applied to the other things on this list
/// - sets, record literals containing items found on this list (including nested)
/// and not:
/// - vars
/// - builtin operators or functions
/// - if/then/else
/// - attribute access, record field access/indexing
#[derive(Debug, Clone)]
pub enum AttrValue {
    /// Bool literal
    BoolLit(bool),
    /// Integer literal
    IntLit(i64),
    /// String literal
    StringLit(SmolStr),
    /// UID literal
    UIDLit(EntityUID),
    /// Extension function call
    ExtFuncCall {
        /// Name of the function being called
        fn_name: Name,
        /// Args to the function
        args: Vec<AttrValue>
    },
    /// Set literal
    Set(Vec<AttrValue>),
    /// Record literal
    Record(HashMap<SmolStr, AttrValue>),
}

impl From<AttrValue> for RestrictedExpr {
    fn from(attrvalue: AttrValue) -> RestrictedExpr {
        match attrvalue {
            AttrValue::BoolLit(b) => RestrictedExpr::val(b),
            AttrValue::IntLit(i) => RestrictedExpr::val(i),
            AttrValue::StringLit(s) => RestrictedExpr::val(s),
            AttrValue::UIDLit(u) => RestrictedExpr::val(u),
            // INVARIANT (MethodCallArgs), only Function Style so no worries here
            AttrValue::ExtFuncCall { fn_name, args } => RestrictedExpr::call_extension_fn(
                fn_name,
                args.into_iter().map(Into::into).collect(),
            ),
            AttrValue::Set(l) => RestrictedExpr::set(l.into_iter().map(Into::into)),
            AttrValue::Record(r) => {
                RestrictedExpr::record(r.into_iter().map(|(k, v)| (k, v.into())))
            }
        }
    }
}

/// Represents an ABAC policy, i.e., fully general
#[derive(Debug, Clone)]
pub struct ABACPolicy(pub GeneratedPolicy);

impl std::fmt::Display for ABACPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Deref for ABACPolicy {
    type Target = GeneratedPolicy;
    fn deref(&self) -> &GeneratedPolicy {
        &self.0
    }
}

impl DerefMut for ABACPolicy {
    fn deref_mut(&mut self) -> &mut GeneratedPolicy {
        &mut self.0
    }
}

impl From<ABACPolicy> for StaticPolicy {
    fn from(abac: ABACPolicy) -> StaticPolicy {
        abac.0.into()
    }
}

/// Represents an ABAC request, i.e., fully general
#[derive(Debug, Clone)]
pub struct ABACRequest(pub Request);

impl std::fmt::Display for ABACRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Deref for ABACRequest {
    type Target = Request;
    fn deref(&self) -> &Request {
        &self.0
    }
}

impl DerefMut for ABACRequest {
    fn deref_mut(&mut self) -> &mut Request {
        &mut self.0
    }
}

impl From<ABACRequest> for ast::Request {
    fn from(abac: ABACRequest) -> ast::Request {
        abac.0.into()
    }
}
