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

use cedar_policy_core::ast::{Id, InternalName};
use cedar_policy_validator::json_schema::{
    ApplySpec, EntityAttributeType, EntityAttributeTypeInternal, EntityAttributes,
    EntityAttributesInternal, EntityType, RecordAttributeType, RecordType, Type, TypeVariant,
};
use cedar_policy_validator::RawName;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use cedar_policy_validator::json_schema;
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
    lhs: json_schema::Fragment<N>,
    rhs: json_schema::Fragment<N>,
) -> Result<(), String> {
    // We need to remove trivial empty namespaces because both `{}`
    // and `{"": {"entityTypes": {}, "actions": {}}}` translate to empty strings
    // in the Cedar schema format
    let mut lhs = lhs;
    let mut rhs = rhs;
    remove_trivial_empty_namespace(&mut lhs);
    remove_trivial_empty_namespace(&mut rhs);
    if lhs.0.len() == rhs.0.len() {
        lhs.0
            .into_iter()
            .map(|(name, lhs_namespace)| {
                let rhs_namespace = rhs
                    .0
                    .get(&name)
                    .ok_or_else(|| format!("`{name:?}` does not exist in RHS schema"))?;
                Equiv::equiv(&lhs_namespace, rhs_namespace)
            })
            .fold(Ok(()), Result::and)
    } else {
        Err("schema differ in number of namespaces".to_string())
    }
}

fn remove_trivial_empty_namespace<N>(schema: &mut json_schema::Fragment<N>) {
    match schema.0.get(&None) {
        Some(def)
            if def.entity_types.is_empty()
                && def.actions.is_empty()
                && def.common_types.is_empty() =>
        {
            schema.0.remove(&None);
        }
        _ => {}
    }
}

pub trait Equiv {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String>;
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

impl<N: Clone + PartialEq + Debug + Display + TypeName + Ord> Equiv for EntityType<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        if !vector_equiv(&lhs.member_of_types, &rhs.member_of_types) {
            Err(format!(
                "lhs and rhs membership are not equal. LHS: [{}], RHS: [{}].",
                lhs.member_of_types.iter().join(","),
                rhs.member_of_types.iter().join(",")
            ))
        } else {
            Equiv::equiv(&lhs.shape, &rhs.shape).map_err(|e| format!("mismatched types: {e}"))
        }
    }
}

impl<N: Clone + PartialEq + TypeName + Debug + Display> Equiv for EntityAttributes<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        match (lhs, rhs) {
            (
                EntityAttributes::RecordAttributes(rca_l),
                EntityAttributes::RecordAttributes(rca_r),
            ) => Equiv::equiv(&rca_l.0, &rca_r.0)
                .map_err(|e| format!("entity attributes not equivalent: {e}")),
            (
                EntityAttributes::EntityAttributes(EntityAttributesInternal {
                    attrs: attrs_l, ..
                }),
                EntityAttributes::EntityAttributes(EntityAttributesInternal {
                    attrs: attrs_r, ..
                }),
            ) => {
                if attrs_l.additional_attributes != attrs_r.additional_attributes {
                    return Err("attributes differ in additional_attributes flag".into());
                }
                Equiv::equiv(&attrs_l.attributes, &attrs_r.attributes)
                    .map_err(|e| format!("entity attributes not equivalent: {e}"))
            }
            (_, _) => {
                // these could still be equivalent in some cases
                unimplemented!()
            }
        }
    }
}

impl<N: Clone + PartialEq + TypeName + Debug + Display> Equiv for EntityAttributeType<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        if lhs.required != rhs.required {
            return Err("attributes differ in required flag".into());
        }
        Equiv::equiv(&lhs.ty, &rhs.ty)
    }
}

impl<N: Clone + PartialEq + TypeName + Debug + Display> Equiv for EntityAttributeTypeInternal<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        match (lhs, rhs) {
            (EntityAttributeTypeInternal::Type(ty_l), EntityAttributeTypeInternal::Type(ty_r)) => {
                Equiv::equiv(ty_l, ty_r)
            }
            (
                EntityAttributeTypeInternal::EAMap {
                    value_type: val_ty_l,
                },
                EntityAttributeTypeInternal::EAMap {
                    value_type: val_ty_r,
                },
            ) => Equiv::equiv(val_ty_l, val_ty_r),
            (_, _) => Err("EAMap is not equivalent to non-EAMap type".into()),
        }
    }
}

impl<N: Clone + PartialEq + TypeName + Debug + Display> Equiv for Type<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        match (lhs, rhs) {
            (Type::Type(lhs), Type::Type(rhs)) => Equiv::equiv(lhs, rhs),
            (Type::CommonTypeRef { type_name: lhs }, Type::CommonTypeRef { type_name: rhs }) => {
                if lhs == rhs {
                    Ok(())
                } else {
                    Err(format!(
                        "common type names do not match: `{lhs}` != `{rhs}`"
                    ))
                }
            }
            (Type::Type(lhs), Type::CommonTypeRef { type_name: rhs }) => Err(format!(
                "lhs is ordinary type `{lhs:?}`, rhs is common type `{rhs}`"
            )),
            (Type::CommonTypeRef { type_name: lhs }, Type::Type(rhs)) => Err(format!(
                "lhs is common type `{lhs}`, rhs is ordinary type `{rhs:?}`"
            )),
        }
    }
}

impl<N: Clone + PartialEq + TypeName + Debug + Display> Equiv for TypeVariant<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        match (lhs, rhs) {
            // Records are equivalent iff
            // A) They have all the same required keys
            // B) Each key has a value that is equivalent
            // C) the `additional_attributes` field is equal
            (
                TypeVariant::Record(RecordType {
                    attributes: lhs_attributes,
                    additional_attributes: lhs_additional_attributes,
                }),
                TypeVariant::Record(RecordType {
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
                TypeVariant::Set {
                    element: lhs_element,
                },
                TypeVariant::Set {
                    element: rhs_element,
                },
            ) => Equiv::equiv(lhs_element.as_ref(), rhs_element.as_ref()),

            // Base types are equivalent to `EntityOrCommon` variants where the type_name is of the
            // form `__cedar::<base type>`
            (TypeVariant::String, TypeVariant::EntityOrCommon { type_name })
            | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::String) => {
                if is_internal_type(type_name, "String") {
                    Ok(())
                } else {
                    Err(format!(
                        "entity-or-common `{type_name}` is not equivalent to String"
                    ))
                }
            }
            (TypeVariant::Long, TypeVariant::EntityOrCommon { type_name })
            | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::Long) => {
                if is_internal_type(type_name, "Long") {
                    Ok(())
                } else {
                    Err(format!(
                        "entity-or-common `{type_name}` is not equivalent to Long"
                    ))
                }
            }
            (TypeVariant::Boolean, TypeVariant::EntityOrCommon { type_name })
            | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::Boolean) => {
                if is_internal_type(type_name, "Bool") {
                    Ok(())
                } else {
                    Err(format!(
                        "entity-or-common `{type_name}` is not equivalent to Boolean"
                    ))
                }
            }
            (TypeVariant::Extension { name }, TypeVariant::EntityOrCommon { type_name })
            | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::Extension { name }) => {
                if is_internal_type(type_name, &name.to_string()) {
                    Ok(())
                } else {
                    Err(format!(
                        "entity-or-common `{type_name}` is not equivalent to Extension `{name}` "
                    ))
                }
            }

            (TypeVariant::Entity { name }, TypeVariant::EntityOrCommon { type_name })
            | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::Entity { name }) => {
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

impl<N: TypeName + Clone + PartialEq + Debug + Display> Equiv for RecordAttributeType<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        if lhs.required != rhs.required {
            return Err(format!("attribute `{lhs:?}` is not equivalent to attribute `{rhs:?}` because of difference in .required"));
        }
        Equiv::equiv(&lhs.ty, &rhs.ty)
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

/// Vectors are equivalent if they contain the same items, regardless of order
fn vector_equiv<N: Ord>(lhs: &[N], rhs: &[N]) -> bool {
    let mut lhs = lhs.iter().collect::<Vec<_>>();
    let mut rhs = rhs.iter().collect::<Vec<_>>();
    lhs.sort();
    rhs.sort();
    lhs == rhs
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
                if (either_empty(&lhs) && either_empty(&rhs)) || Equiv::equiv(lhs, rhs).is_ok() {
                    Ok(())
                } else {
                    Err(format!(
                        "Mismatched applies to in `{name}`. lhs : `{:?}`,rhs: `{:?}`",
                        lhs, rhs
                    ))
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

impl<N: TypeName + Clone + PartialEq + Ord + Debug + Display> Equiv for ApplySpec<N> {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        // ApplySpecs are equivalent iff
        // A) the principal and resource type lists are equal
        // B) the context shapes are equivalent
        if Equiv::equiv(&lhs.context.0, &rhs.context.0).is_ok()
            && vector_equiv(&lhs.principal_types, &rhs.principal_types)
            && vector_equiv(&lhs.resource_types, &rhs.resource_types)
        {
            Ok(())
        } else {
            Err("ApplySpecs are not equivalent".into())
        }
    }
}

fn either_empty<N>(spec: &json_schema::ApplySpec<N>) -> bool {
    spec.principal_types.is_empty() || spec.resource_types.is_empty()
}

impl Equiv for cedar_policy_validator::ValidatorSchema {
    fn equiv(lhs: &Self, rhs: &Self) -> Result<(), String> {
        // Just compare entity attribute types and context types are equivalent
        let entity_attr_tys_lhs: HashMap<
            &cedar_drt::ast::EntityType,
            HashMap<&smol_str::SmolStr, &cedar_policy_validator::types::AttributeType>,
        > = HashMap::from_iter(
            lhs.entity_types()
                .map(|(name, ty)| (name, HashMap::from_iter(ty.attributes()))),
        );
        let entity_attr_tys_rhs = HashMap::from_iter(
            rhs.entity_types()
                .map(|(name, ty)| (name, HashMap::from_iter(ty.attributes()))),
        );
        if entity_attr_tys_lhs != entity_attr_tys_rhs {
            return Err("entity attributes not equivalent".into());
        }
        let context_ty_lhs: HashSet<&cedar_policy_validator::types::Type> = HashSet::from_iter(
            lhs.action_entities()
                .unwrap()
                .iter()
                .map(|e| lhs.get_action_id(e.uid()).unwrap().context_type()),
        );
        let context_ty_rhs: HashSet<&cedar_policy_validator::types::Type> = HashSet::from_iter(
            rhs.action_entities()
                .unwrap()
                .iter()
                .map(|e| lhs.get_action_id(e.uid()).unwrap().context_type()),
        );
        if context_ty_lhs != context_ty_rhs {
            return Err("contexts not equivalent".into());
        }
        Ok(())
    }
}
