/*
 * Copyright Cedar Contributors
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

use crate::collections::HashMap;
use crate::err::{while_doing, Error, Result};
use crate::policy::GeneratedPolicy;
use crate::request::Request;
use crate::settings::*;
use crate::size_hint_utils::size_hint_for_choose;
use crate::{accum, gen, gen_inner, uniform};
use arbitrary::{Arbitrary, Unstructured};
use ast::{EntityUID, Name, RestrictedExpr, StaticPolicy};
use cedar_policy_core::ast;
use cedar_policy_core::extensions;
use serde::Serialize;
use smol_str::SmolStr;
use std::cell::RefCell;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::ops::{Deref, DerefMut};
use thiserror::Error;

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
    unknowns: RefCell<HashMap<String, (Type, ast::Value)>>,
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
    pub fn mapping(self) -> impl Iterator<Item = (String, ast::Value)> {
        self.unknowns.take().into_iter().map(|(k, (_, v))| (k, v))
    }

    /// Create a new unknown with the given `Type` and `Value`. Returns the new
    /// name as a `String`
    pub fn alloc(&self, t: Type, v: ast::Value) -> String {
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

#[derive(Debug, Clone, Copy)]
struct BiasedI64(i64);

impl<'a> Arbitrary<'a> for BiasedI64 {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(gen!(u,
            1 => i64::MAX,
            1 => i64::MIN,
            1 => -1,
            1 => 0,
            6 => <i64 as Arbitrary>::arbitrary(u)?
        )
        .into())
    }
}

impl From<i64> for BiasedI64 {
    fn from(value: i64) -> Self {
        Self(value)
    }
}

impl From<BiasedI64> for i64 {
    fn from(value: BiasedI64) -> Self {
        value.0
    }
}

impl<'a> Arbitrary<'a> for ConstantPool {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let sc: Vec<String> = u.arbitrary()?;
        Ok(Self {
            int_constants: <Vec<BiasedI64> as Arbitrary>::arbitrary(u)
                .map(|bis| bis.into_iter().map(|bi| bi.into()).collect::<Vec<i64>>())?,
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
                .map_err(|e| while_doing("getting an arbitrary int constant".into(), e))
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
            .map_err(|e| while_doing("getting an arbitrary string constant".into(), e))
            .or_else(|_| arbitrary_string(u, Some(bound)))
    }

    /// Get an arbitrary string constant from the pool.
    /// If there are no string constants in the pool, get a purely arbitrary string constant
    pub fn arbitrary_string_constant(&self, u: &mut Unstructured<'_>) -> Result<SmolStr> {
        u.choose(&self.string_constants).cloned().or_else(|_| {
            u.arbitrary::<String>()
                .map(|s| s.into())
                .map_err(|e| while_doing("getting an arbitrary string constant".into(), e))
        })
    }

    /// Produce a RHS of a like operation
    /// It's derived from a random string constant in the pool: We perform transformations over it such as adding a char, deleting a char and adding a wildcard star.
    pub fn arbitrary_pattern_literal(&self, u: &mut Unstructured<'_>) -> Result<ast::Pattern> {
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
        Ok(ast::Pattern::from(pattern))
    }

    // Generate a valid IPv4 net representation
    fn arbitrary_ipv4_str(&self, u: &mut Unstructured<'_>) -> Result<String> {
        let ip: Ipv4Addr = u.arbitrary()?;
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
        let ip: Ipv6Addr = u.arbitrary()?;
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
        let i = self.arbitrary_int_constant(u)?;
        mutate_str(
            u,
            // Replicate from Core
            &format!("{}.{}", i / i64::pow(10, 4), (i % i64::pow(10, 4)).abs()),
        )
        .map(SmolStr::new)
    }

    // Generate a roughly valid datetime string
    fn arbitrary_datetime_str_inner(&self, u: &mut Unstructured<'_>) -> Result<String> {
        let mut result = String::new();
        // Generate YYYY-MM-DD
        let y = u.int_in_range(0..=9999)?;
        let m = u.int_in_range(1..=12)?;
        let d = u.int_in_range(1..=31)?;
        result.push_str(&format!("{:04}-{:02}-{:02}", y, m, d));
        // There's a 25% chance where just a date is generated
        if u.ratio(1, 4)? {
            return Ok(result);
        }
        // Generate hh:mm:ss
        result.push('T');
        let h = u.int_in_range(0..=23)?;
        let m = u.int_in_range(0..=59)?;
        let s = u.int_in_range(0..=59)?;
        result.push_str(&format!("{:02}:{:02}:{:02}", h, m, s));
        match u.int_in_range(0..=3)? {
            0 => {
                // end the string with `Z`
                result.push('Z');
            }
            1 => {
                // Generate a millisecond and end the string
                let ms = u.int_in_range(0..=999)?;
                result.push_str(&format!(".{:03}Z", ms));
            }
            2 => {
                // Generate an offset
                let sign = if u.arbitrary()? { '+' } else { '-' };
                let hh = u.int_in_range(0..=14)?;
                let mm = u.int_in_range(0..=59)?;
                result.push_str(&format!("{sign}{:02}{:02}", hh, mm));
            }
            3 => {
                // Generate a millisecond and an offset
                let ms = u.int_in_range(0..=999)?;
                let sign = if u.arbitrary()? { '+' } else { '-' };
                let hh = u.int_in_range(0..=14)?;
                let mm = u.int_in_range(0..=59)?;
                result.push_str(&format!(".{:03}{sign}{:02}{:02}", ms, hh, mm));
            }
            _ => {
                unreachable!("the number is from 0 to 3")
            }
        }
        Ok(result)
    }

    /// Generate a roughly valid datetime string and mutate it
    pub fn arbitrary_datetime_str(&self, u: &mut Unstructured<'_>) -> Result<SmolStr> {
        let result = self.arbitrary_datetime_str_inner(u)?;
        mutate_str(u, &result).map(Into::into)
    }

    /// Generate a roughly valid duration string and mutate it
    pub fn arbitrary_duration_str(&self, u: &mut Unstructured<'_>) -> Result<SmolStr> {
        let mut result = String::new();
        // flip a coin and add `-`
        if u.arbitrary()? {
            result.push('-');
        }
        for suffix in ["d", "h", "m", "s", "ms"] {
            // Generate a number with certain suffix
            if u.arbitrary()? {
                let i = self.arbitrary_int_constant(u)?;
                result.push_str(&format!("{}{suffix}", (i as i128).abs()));
            }
        }
        // If none of the units is generated, generate a random milliseconds
        if result.is_empty() || result == "-" {
            let i = self.arbitrary_int_constant(u)?;
            result.push_str(&format!("{}ms", (i as i128).abs()));
        }
        mutate_str(u, &result).map(Into::into)
    }

    /// size hint for arbitrary_string_constant()
    pub fn arbitrary_string_constant_size_hint(_depth: usize) -> (usize, Option<usize>) {
        size_hint_for_choose(None)
    }
}

/// Generate an arbitrary string of up to `bound` size
fn arbitrary_string(u: &mut Unstructured<'_>, bound: Option<usize>) -> Result<SmolStr> {
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
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("datetime")
                        .expect("should be a valid identifier"),
                    is_constructor: true,
                    parameter_types: vec![Type::string()],
                    return_ty: Type::datetime(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("offset")
                        .expect("should be a valid identifier"),
                    is_constructor: true,
                    parameter_types: vec![Type::datetime(), Type::duration()],
                    return_ty: Type::datetime(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("durationSince")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::datetime(), Type::datetime()],
                    return_ty: Type::duration(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("toDate")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::datetime()],
                    return_ty: Type::datetime(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("toTime")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::datetime()],
                    return_ty: Type::duration(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("duration")
                        .expect("should be a valid identifier"),
                    is_constructor: true,
                    parameter_types: vec![Type::string()],
                    return_ty: Type::duration(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("toMilliseconds")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::duration()],
                    return_ty: Type::long(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("toSeconds")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::duration()],
                    return_ty: Type::long(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("toMinutes")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::duration()],
                    return_ty: Type::long(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("toHours")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::duration()],
                    return_ty: Type::long(),
                },
                AvailableExtensionFunction {
                    name: Name::parse_unqualified_name("toDays")
                        .expect("should be a valid identifier"),
                    is_constructor: false,
                    parameter_types: vec![Type::duration()],
                    return_ty: Type::long(),
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
            .map_err(|e| while_doing("getting arbitrary extfunc constructor".into(), e))
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
            .map_err(|e| while_doing("getting arbitrary extfunc".into(), e))
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
                    doing_what: format!("getting extfunc constructors for type {ty:?}"),
                })?;
        u.choose(choices).map_err(|e| {
            while_doing(
                format!("getting arbitrary extfunc constructor with return type {ty:?}"),
                e,
            )
        })
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
                doing_what: format!("getting arbitrary extfunc with return type {ty:?}"),
            })?;
        u.choose(choices).map_err(|e| {
            while_doing(
                format!("getting arbitrary extfunc with return type {ty:?}"),
                e,
            )
        })
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
    /// datetime
    DateTime,
    /// duration
    Duration,
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
    /// datetime type
    pub fn datetime() -> Self {
        Type::DateTime
    }
    /// duration type
    pub fn duration() -> Self {
        Type::Duration
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

impl TryFrom<Type> for ast::Type {
    type Error = NotEnoughTypeInformation;
    fn try_from(ty: Type) -> std::result::Result<ast::Type, Self::Error> {
        match ty {
            Type::Bool => Ok(ast::Type::Bool),
            Type::Long => Ok(ast::Type::Long),
            Type::String => Ok(ast::Type::String),
            Type::Set(_) => Ok(ast::Type::Set),
            Type::Record => Ok(ast::Type::Record),
            Type::Entity => Err(NotEnoughTypeInformation::NeedEntityTypename),
            Type::IPAddr => Ok(ast::Type::Extension {
                name: extensions::ipaddr::extension().name().clone(),
            }),
            Type::Decimal => Ok(ast::Type::Extension {
                name: extensions::decimal::extension().name().clone(),
            }),
            Type::DateTime => Ok(ast::Type::Extension {
                name: extensions::datetime::extension().name().clone(),
            }),
            Type::Duration => Ok(ast::Type::Extension {
                name: "duration".parse().unwrap(),
            }),
        }
    }
}

/// Error encountered when trying to convert `Type` to `ast::Type` but there
/// isn't enough type information to determine which `ast::Type` to return.
#[derive(Debug, Error)]
pub enum NotEnoughTypeInformation {
    /// `Type` doesn't distinguish entities with different typenames, but
    /// `ast::Type` needs the entity typename
    #[error("can't convert to `ast::Type` because we need the entity typename")]
    NeedEntityTypename,
}

/// attribute values are restricted expressions: just
/// - bool literals
/// - int literals
/// - string literals
/// - UID literals
/// - extension function calls applied to the other things on this list
/// - sets, record literals containing items found on this list (including nested)
///
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
        args: Vec<AttrValue>,
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
                args.into_iter().map(Into::into),
            ),
            AttrValue::Set(l) => RestrictedExpr::set(l.into_iter().map(Into::into)),
            AttrValue::Record(r) => {
                RestrictedExpr::record(r.into_iter().map(|(k, v)| (k, v.into())))
                    .expect("can't have duplicate keys, because the keys are the same as in the input `r` which was already a HashMap")
            }
        }
    }
}

/// Represents an ABAC policy, i.e., fully general
#[derive(Debug, Clone, Serialize)]
#[serde(transparent)]
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

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use arbitrary::{Arbitrary, Unstructured};
    use cedar_policy_core::{
        ast::{Expr, Name, Request, Value},
        entities::Entities,
        evaluator::Evaluator,
        extensions::Extensions,
    };
    use rand::{rngs::StdRng, RngCore, SeedableRng};
    use smol_str::SmolStr;

    use super::ConstantPool;

    // get validate string count
    #[track_caller]
    fn evaluate_batch(strs: &[SmolStr], constructor: Name) -> usize {
        let dummy_euid: Arc<cedar_policy_core::ast::EntityUID> =
            Arc::new(r#"A::"""#.parse().unwrap());
        let dummy_request = Request::new_unchecked(
            cedar_policy_core::ast::EntityUIDEntry::Known {
                euid: dummy_euid.clone(),
                loc: None,
            },
            cedar_policy_core::ast::EntityUIDEntry::Known {
                euid: dummy_euid.clone(),
                loc: None,
            },
            cedar_policy_core::ast::EntityUIDEntry::Known {
                euid: dummy_euid.clone(),
                loc: None,
            },
            None,
        );
        let entities = Entities::new();
        let evaluator = Evaluator::new(dummy_request, &entities, Extensions::all_available());
        let valid_strs: Vec<_> = strs
            .into_iter()
            .filter(|s| {
                evaluator
                    .interpret(
                        &Expr::call_extension_fn(
                            constructor.clone(),
                            vec![Value::from(s.to_owned().to_owned()).into()],
                        ),
                        &HashMap::new(),
                    )
                    .is_ok()
            })
            .collect();
        valid_strs.len()
    }

    #[test]
    fn test_valid_extension_value_ratio() {
        let mut rng = StdRng::seed_from_u64(666);
        let mut bytes = [0; 4096];
        rng.fill_bytes(&mut bytes);
        let mut u = Unstructured::new(&bytes);
        let pool = ConstantPool::arbitrary(&mut u).expect("should not fail");

        let datetime_strs: Vec<_> = (0..100)
            .map(|_| {
                pool.arbitrary_datetime_str(&mut u)
                    .expect("should not fail")
            })
            .collect();
        let valid_datetime_count = evaluate_batch(&datetime_strs, "datetime".parse().unwrap());
        println!("{}", valid_datetime_count);

        let duration_strs: Vec<_> = (0..100)
            .map(|_| {
                pool.arbitrary_duration_str(&mut u)
                    .expect("should not fail")
            })
            .collect();
        let valid_duration_count = evaluate_batch(&duration_strs, "duration".parse().unwrap());
        println!("{}", valid_duration_count);
    }
}
