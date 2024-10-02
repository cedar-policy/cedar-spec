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

use cedar_policy_core::ast::{Id, InternalName, Name};
use cedar_policy_validator::json_schema;
use cedar_policy_validator::RawName;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use std::fmt::{Debug, Display};
use std::hash::Hash;

/// Check if two schema fragments are equivalent, modulo empty apply specs.
/// We do this because there are schemas that are representable in the JSON that are not
/// representable in the Cedar syntax. All of these non-representable schemas
/// are equivalent to one that is representable.
///
/// Example:
/// You can have a JSON schema with an action that has no applicable principals and some applicable
/// resources.
/// In the Cedar syntax, you can't. The only way to write an action with no applicable
/// principals is:
/// ```cedarschema
/// action a;
/// ```
/// Specifying an action with no applicable principals and no applicable resources.
///
/// However, this is _equivalent_. An action that can't be applied to any principals can't ever be
/// used. Whether or not there are applicable resources is useless.
///
pub fn equivalence_check<N: Clone + PartialEq + Debug + Display + TypeName + Ord>(
    lhs: &json_schema::Fragment<N>,
    rhs: &json_schema::Fragment<N>,
) -> Result<(), String> {
    if nontrivial_namespaces(lhs).count() == nontrivial_namespaces(rhs).count() {
        nontrivial_namespaces(lhs)
            .map(|(name, lhs_namespace)| {
                let rhs_namespace = rhs
                    .0
                    .get(&name)
                    .ok_or_else(|| format!("namespace `{name:?}` does not exist in RHS schema"))?;
                Equiv::equiv(lhs_namespace, rhs_namespace)
            })
            .fold(Ok(()), Result::and)
    } else {
        Err("schemas differ in number of namespaces".to_string())
    }
}

/// Iterate over the namespace defs in the [`json_schema::Fragment`], omitting
/// the empty namespace if it has no items.
///
/// We need to ignore trivial empty namespaces because both `{}`
/// and `{"": {"entityTypes": {}, "actions": {}}}` translate to empty strings
/// in the Cedar schema format
fn nontrivial_namespaces<N>(
    frag: &json_schema::Fragment<N>,
) -> impl Iterator<Item = (&Option<Name>, &json_schema::NamespaceDefinition<N>)> {
    frag.0
        .iter()
        .filter(|(name, nsdef)| name.is_some() || !is_trivial_namespace(nsdef))
}

fn is_trivial_namespace<N>(nsdef: &json_schema::NamespaceDefinition<N>) -> bool {
    nsdef.entity_types.is_empty() && nsdef.actions.is_empty() && nsdef.common_types.is_empty()
}

pub trait Equiv {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String>;
}

impl<'a, T: Equiv> Equiv for &'a T {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        Equiv::equiv(*lhs, *rhs)
    }
}

impl<N: Clone + PartialEq + Debug + Display + TypeName + Ord> Equiv
    for json_schema::NamespaceDefinition<N>
{
    fn equiv(
        lhs: &json_schema::NamespaceDefinition<N>,
        rhs: &json_schema::NamespaceDefinition<N>,
    ) -> Result<(), String> {
        Equiv::equiv(&lhs.entity_types, &rhs.entity_types)?;
        if &lhs.common_types != &rhs.common_types {
            Err("Common types differ".to_string())
        } else if lhs.actions.len() != rhs.actions.len() {
            Err("Different number of actions".to_string())
        } else {
            lhs.actions
                .iter()
                .map(|(name, lhs_action)| {
                    let rhs_action = rhs
                        .actions
                        .get(name)
                        .ok_or_else(|| format!("Action `{name}` not present on rhs"))?;
                    action_type_equivalence(name.as_ref(), lhs_action, rhs_action)
                })
                .fold(Ok(()), Result::and)
        }
    }
}

/// `Equiv` for `HashSet` requires that the items in the set are exactly equal,
/// not equivalent by `Equiv`. (It would be hard to line up which item is
/// supposed to correspond to which, given an arbitrary `Equiv` implementation.)
impl<V: Eq + Hash + Display> Equiv for HashSet<V> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        if lhs != rhs {
            let missing_elems = lhs.symmetric_difference(&rhs).join(", ");
            Err(format!("missing set elements: {missing_elems}"))
        } else {
            Ok(())
        }
    }
}

/// `Equiv` for `BTreeSet` requires that the items in the set are exactly equal,
/// not equivalent by `Equiv`. (It would be hard to line up which item is
/// supposed to correspond to which, given an arbitrary `Equiv` implementation.)
impl<V: Eq + Ord + Display> Equiv for BTreeSet<V> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        if lhs != rhs {
            let missing_elems = lhs.symmetric_difference(&rhs).join(", ");
            Err(format!("missing set elements: {missing_elems}"))
        } else {
            Ok(())
        }
    }
}

impl<K: Eq + Hash + Display, V: Equiv> Equiv for HashMap<K, V> {
    fn equiv(lhs: &HashMap<K, V>, rhs: &HashMap<K, V>) -> Result<(), String> {
        if lhs.len() == rhs.len() {
            let errors = lhs
                .iter()
                .filter_map(|(k, lhs_v)| match rhs.get(k) {
                    Some(rhs_v) => Equiv::equiv(lhs_v, rhs_v).err(),
                    None => Some(format!("`{k}` missing from rhs")),
                })
                .collect::<Vec<_>>();
            if errors.is_empty() {
                Ok(())
            } else {
                Err(format!(
                    "Found the following mismatches: {}",
                    errors.into_iter().join("\n")
                ))
            }
        } else {
            let lhs_keys: HashSet<_> = lhs.keys().collect();
            let rhs_keys: HashSet<_> = rhs.keys().collect();
            let missing_keys = lhs_keys.symmetric_difference(&rhs_keys).join(", ");
            Err(format!("Missing keys: {missing_keys}"))
        }
    }
}

impl<K: Eq + Ord + Display, V: Equiv> Equiv for BTreeMap<K, V> {
    fn equiv(lhs: &BTreeMap<K, V>, rhs: &BTreeMap<K, V>) -> Result<(), String> {
        if lhs.len() == rhs.len() {
            let errors = lhs
                .iter()
                .filter_map(|(k, lhs_v)| match rhs.get(k) {
                    Some(rhs_v) => Equiv::equiv(lhs_v, rhs_v).err(),
                    None => Some(format!("`{k}` missing from rhs")),
                })
                .collect::<Vec<_>>();
            if errors.is_empty() {
                Ok(())
            } else {
                Err(format!(
                    "Found the following mismatches: {}",
                    errors.into_iter().join("\n")
                ))
            }
        } else {
            let lhs_keys: BTreeSet<_> = lhs.keys().collect();
            let rhs_keys: BTreeSet<_> = rhs.keys().collect();
            let missing_keys = lhs_keys.symmetric_difference(&rhs_keys).join(", ");
            Err(format!("Missing keys: {missing_keys}"))
        }
    }
}

impl<N: Clone + PartialEq + Debug + Display + TypeName + Ord> Equiv for json_schema::EntityType<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        Equiv::equiv(
            &lhs.member_of_types.iter().collect::<BTreeSet<_>>(),
            &rhs.member_of_types.iter().collect::<BTreeSet<_>>(),
        )
        .map_err(|e| format!("memberOfTypes are not equal: {e}"))?;
        Equiv::equiv(&lhs.shape, &rhs.shape).map_err(|e| format!("mismatched types: {e}"))
    }
}

impl Equiv for cedar_policy_validator::ValidatorEntityType {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        Equiv::equiv(&lhs.descendants, &rhs.descendants)?;
        Equiv::equiv(
            &lhs.attributes().collect::<HashMap<_, _>>(),
            &rhs.attributes().collect::<HashMap<_, _>>(),
        )?;
        Ok(())
    }
}

impl<N: Clone + PartialEq + TypeName + Debug + Display> Equiv for json_schema::TypeOfAttribute<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        if lhs.required != rhs.required {
            return Err("attributes differ in required flag".into());
        }
        Equiv::equiv(&lhs.ty, &rhs.ty)
    }
}

impl Equiv for cedar_policy_validator::types::AttributeType {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        if lhs.is_required != rhs.is_required {
            return Err("attributes differ in required flag".into());
        }
        Equiv::equiv(&lhs.attr_type, &rhs.attr_type)
    }
}

impl<N: Clone + PartialEq + TypeName + Debug + Display> Equiv for json_schema::Type<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        match (lhs, rhs) {
            (Self::Type(lhs), Self::Type(rhs)) => Equiv::equiv(lhs, rhs),
            (Self::CommonTypeRef { type_name: lhs }, Self::CommonTypeRef { type_name: rhs }) => {
                if lhs == rhs {
                    Ok(())
                } else {
                    Err(format!(
                        "common type names do not match: `{lhs}` != `{rhs}`"
                    ))
                }
            }
            (Self::Type(tv), Self::CommonTypeRef { type_name })
            | (Self::CommonTypeRef { type_name }, Self::Type(tv)) => {
                match tv {
                    json_schema::TypeVariant::EntityOrCommon {
                        type_name: tv_type_name,
                    } if type_name == tv_type_name => {
                        // Consider common-type equivalent to entity-or-common of the same name
                        Ok(())
                    }
                    _ => Err(format!(
                        "Common-type `{type_name}` is not equivalent to non-common-type {tv:?}"
                    )),
                }
            }
        }
    }
}

impl Equiv for cedar_policy_validator::types::Type {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        if lhs != rhs {
            Err(format!("types are not equal: {lhs} != {rhs}"))
        } else {
            Ok(())
        }
    }
}

impl<N: Clone + PartialEq + TypeName + Debug + Display> Equiv for json_schema::TypeVariant<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        match (lhs, rhs) {
            // Records are equivalent iff
            // A) They have all the same required keys
            // B) Each key has a value that is equivalent
            // C) the `additional_attributes` field is equal
            (
                Self::Record(json_schema::RecordType {
                    attributes: lhs_attributes,
                    additional_attributes: lhs_additional_attributes,
                }),
                Self::Record(json_schema::RecordType {
                    attributes: rhs_attributes,
                    additional_attributes: rhs_additional_attributes,
                }),
            ) => {
                let lhs_required_keys = lhs_attributes.keys().collect::<HashSet<_>>();
                let rhs_required_keys = rhs_attributes.keys().collect::<HashSet<_>>();
                if lhs_required_keys != rhs_required_keys {
                    return Err(
                        "records are not equivalent because they have different keysets".into(),
                    );
                }
                if lhs_additional_attributes != rhs_additional_attributes {
                    return Err("records are not equivalent because they have different additional_attributes flags".into());
                }
                lhs_attributes
                    .into_iter()
                    .map(|(key, lhs)| Equiv::equiv(lhs, rhs_attributes.get(key).unwrap()))
                    .collect::<Result<(), String>>()
            }
            // Sets are equivalent if their elements are equivalent
            (
                Self::Set {
                    element: lhs_element,
                },
                Self::Set {
                    element: rhs_element,
                },
            ) => Equiv::equiv(lhs_element.as_ref(), rhs_element.as_ref()),

            // Base types are equivalent to `EntityOrCommon` variants where the type_name is of the
            // form `__cedar::<base type>`
            (Self::String, Self::EntityOrCommon { type_name })
            | (Self::EntityOrCommon { type_name }, Self::String) => {
                if is_internal_type(type_name, "String") {
                    Ok(())
                } else {
                    Err(format!(
                        "entity-or-common `{type_name}` is not equivalent to String"
                    ))
                }
            }
            (Self::Long, Self::EntityOrCommon { type_name })
            | (Self::EntityOrCommon { type_name }, Self::Long) => {
                if is_internal_type(type_name, "Long") {
                    Ok(())
                } else {
                    Err(format!(
                        "entity-or-common `{type_name}` is not equivalent to Long"
                    ))
                }
            }
            (Self::Boolean, Self::EntityOrCommon { type_name })
            | (Self::EntityOrCommon { type_name }, Self::Boolean) => {
                if is_internal_type(type_name, "Bool") {
                    Ok(())
                } else {
                    Err(format!(
                        "entity-or-common `{type_name}` is not equivalent to Boolean"
                    ))
                }
            }
            (Self::Extension { name }, Self::EntityOrCommon { type_name })
            | (Self::EntityOrCommon { type_name }, Self::Extension { name }) => {
                if is_internal_type(type_name, &name.to_string()) {
                    Ok(())
                } else {
                    Err(format!(
                        "entity-or-common `{type_name}` is not equivalent to Extension `{name}` "
                    ))
                }
            }

            (Self::Entity { name }, Self::EntityOrCommon { type_name })
            | (Self::EntityOrCommon { type_name }, Self::Entity { name }) => {
                if type_name == name {
                    Ok(())
                } else {
                    Err(format!(
                        "entity `{name}` is not equivalent to entity-or-common `{type_name}`"
                    ))
                }
            }

            // Types that are exactly equal are of course equivalent
            (lhs, rhs) => {
                if lhs == rhs {
                    Ok(())
                } else {
                    Err("types are not equivalent".into())
                }
            }
        }
    }
}

impl<N: TypeName + Clone + PartialEq + Debug + Display> Equiv
    for json_schema::AttributesOrContext<N>
{
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        Equiv::equiv(&lhs.0, &rhs.0)
    }
}

/// Is the given type name the `__cedar` alias for an internal type
/// This is true iff
/// A) the namespace is exactly `__cedar`
/// B) the basename matches the passed string
fn is_internal_type<N: TypeName + Clone>(type_name: &N, expected: &str) -> bool {
    let qualed = type_name.clone().qualify();
    (qualed.basename().to_string() == expected)
        && qualed
            .namespace_components()
            .map(Id::to_string)
            .collect_vec()
            == vec!["__cedar"]
}

/// Trait for taking either `N` to a concrete type we can do equality over
pub trait TypeName {
    fn qualify(self) -> InternalName;
}

// For [`RawName`] we just qualify with no namespace
impl TypeName for RawName {
    fn qualify(self) -> InternalName {
        self.qualify_with(None)
    }
}

// For [`InternalName`] we just return the name as it exists
impl TypeName for InternalName {
    fn qualify(self) -> InternalName {
        self
    }
}

fn action_type_equivalence<N: PartialEq + Debug + Display + Clone + TypeName + Ord>(
    name: &str,
    lhs: &json_schema::ActionType<N>,
    rhs: &json_schema::ActionType<N>,
) -> Result<(), String> {
    if &lhs.attributes != &rhs.attributes {
        Err(format!("Attributes don't match for `{name}`"))
    } else if &lhs.member_of != &rhs.member_of {
        Err(format!("Member of don't match for `{name}`"))
    } else {
        match (&lhs.applies_to, &rhs.applies_to) {
            (None, None) => Ok(()),
            (Some(lhs), Some(rhs)) => {
                // If either of them has at least one empty appliesTo list, the other must have the same attribute.
                if either_empty(&lhs) && either_empty(&rhs) {
                    Ok(())
                } else {
                    match Equiv::equiv(lhs, rhs) {
                        Ok(()) => Ok(()),
                        Err(e) => Err(format!("Mismatched appliesTo in `{name}`: {e}")),
                    }
                }
            }
            // An action w/ empty applies to list is equivalent to an action with _no_ applies to
            // section at all.
            // This is because neither action can be legally applied to any principal/resources.
            (Some(applies_to), None) | (None, Some(applies_to)) if either_empty(applies_to) => {
                Ok(())
            }
            (Some(_), None) => Err(format!(
                "Mismatched applies to in `{name}`, lhs was `Some`, `rhs` was `None`"
            )),
            (None, Some(_)) => Err(format!(
                "Mismatched applies to in `{name}`, lhs was `None`, `rhs` was `Some`"
            )),
        }
    }
}

impl<N: TypeName + Clone + PartialEq + Ord + Debug + Display> Equiv for json_schema::ApplySpec<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        // ApplySpecs are equivalent iff
        // A) the principal and resource type lists are equal
        // B) the context shapes are equivalent
        Equiv::equiv(&lhs.context.0, &rhs.context.0)?;
        Equiv::equiv(
            &lhs.principal_types.iter().collect::<BTreeSet<_>>(),
            &rhs.principal_types.iter().collect::<BTreeSet<_>>(),
        )?;
        Equiv::equiv(
            &lhs.resource_types.iter().collect::<BTreeSet<_>>(),
            &rhs.resource_types.iter().collect::<BTreeSet<_>>(),
        )?;
        Ok(())
    }
}

fn either_empty<N>(spec: &json_schema::ApplySpec<N>) -> bool {
    spec.principal_types.is_empty() || spec.resource_types.is_empty()
}

impl Equiv for cedar_policy_validator::ValidatorSchema {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        Equiv::equiv(
            &lhs.entity_types().collect::<HashMap<_, _>>(),
            &rhs.entity_types().collect::<HashMap<_, _>>(),
        )
        .map_err(|e| format!("entity attributes are not equivalent: {e}"))?;
        Equiv::equiv(
            &lhs.action_entities()
                .unwrap()
                .iter()
                .map(|e| lhs.get_action_id(e.uid()).unwrap().context_type())
                .collect::<HashSet<_>>(),
            &rhs.action_entities()
                .unwrap()
                .iter()
                .map(|e| rhs.get_action_id(e.uid()).unwrap().context_type())
                .collect::<HashSet<_>>(),
        )
        .map_err(|e| format!("contexts are not equivalent: {e}"))?;
        Ok(())
    }
}
