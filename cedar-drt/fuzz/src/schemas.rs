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

use cedar_policy_core::ast::{Id, InternalName, UnreservedId};
use cedar_policy_validator::json_schema::{
    ApplySpec, EntityType, Type, TypeOfAttribute, TypeVariant,
};
use cedar_policy_validator::RawName;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

use cedar_policy_validator::json_schema;
use std::fmt::{Debug, Display};

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
                namespace_equivalence(lhs_namespace, rhs_namespace.clone())
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

fn namespace_equivalence<N: Clone + PartialEq + Debug + Display + TypeName + Ord>(
    lhs: json_schema::NamespaceDefinition<N>,
    rhs: json_schema::NamespaceDefinition<N>,
) -> Result<(), String> {
    entity_types_equivalence(lhs.entity_types, rhs.entity_types)?;
    if lhs.common_types != rhs.common_types {
        Err("Common types differ".to_string())
    } else if lhs.actions.len() != rhs.actions.len() {
        Err("Different number of actions".to_string())
    } else {
        lhs.actions
            .into_iter()
            .map(|(name, lhs_action)| {
                let rhs_action = rhs
                    .actions
                    .get(&name)
                    .ok_or_else(|| format!("Action `{name}` not present on rhs"))?;
                action_type_equivalence(name.as_ref(), lhs_action, rhs_action.clone())
            })
            .fold(Ok(()), Result::and)
    }
}

type EntityData<N> = HashMap<UnreservedId, EntityType<N>>;

fn entity_types_equivalence<N: Clone + PartialEq + Debug + Display + TypeName + Ord>(
    lhs: EntityData<N>,
    rhs: EntityData<N>,
) -> Result<(), String> {
    if lhs.len() == rhs.len() {
        let errors = lhs
            .into_iter()
            .filter_map(|lhs| entity_type_equivalence(lhs, &rhs).err())
            .collect::<Vec<_>>();
        if errors.is_empty() {
            Ok(())
        } else {
            Err(format!(
                "Found the following entity type mismatches: {}",
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

fn entity_type_equivalence<N: Clone + PartialEq + Debug + Display + TypeName + Ord>(
    (name, lhs_type): (UnreservedId, EntityType<N>),
    rhs: &EntityData<N>,
) -> Result<(), String> {
    let rhs_type = rhs
        .get(&name)
        .ok_or_else(|| format!("Type `{name}` was missing from right-hand-side"))?;

    if vector_equiv(&lhs_type.member_of_types, &rhs_type.member_of_types) {
        Err(format!(
            "For `{name}`: lhs and rhs membership are not equal. LHS: [{}], RHS: [{}].",
            lhs_type
                .member_of_types
                .into_iter()
                .map(|id| id.to_string())
                .join(","),
            rhs_type
                .member_of_types
                .iter()
                .map(|id| id.to_string())
                .join(",")
        ))
    } else if shape_equiv(&lhs_type.shape.0, &rhs_type.shape.0) {
        Ok(())
    } else {
        Err(format!("`{name}` has mismatched types"))
    }
}

fn shape_equiv<N: Clone + PartialEq + TypeName>(lhs: &Type<N>, rhs: &Type<N>) -> bool {
    match (lhs, rhs) {
        (Type::Type(lhs), Type::Type(rhs)) => type_varient_equiv(lhs, rhs),
        (Type::CommonTypeRef { type_name: lhs }, Type::CommonTypeRef { type_name: rhs }) => {
            lhs == rhs
        }
        _ => false,
    }
}

/// Type Variant equivalence. See the arms of each match for details
fn type_varient_equiv<N: Clone + PartialEq + TypeName>(
    lhs: &TypeVariant<N>,
    rhs: &TypeVariant<N>,
) -> bool {
    match (lhs, rhs) {
        // Records are equivalent iff
        // A) They have all the same required keys
        // B) Each key has a value that is equivalent
        // C) the `additional_attributes` field is equal
        (
            TypeVariant::Record {
                attributes: lhs_attributes,
                additional_attributes: lhs_additional_attributes,
            },
            TypeVariant::Record {
                attributes: rhs_attributes,
                additional_attributes: rhs_additional_attributes,
            },
        ) => {
            let lhs_required_keys = lhs_attributes.keys().collect::<HashSet<_>>();
            let rhs_required_keys = rhs_attributes.keys().collect::<HashSet<_>>();
            if lhs_required_keys == rhs_required_keys {
                lhs_attributes
                    .into_iter()
                    .all(|(key, lhs)| attribute_equiv(&lhs, rhs_attributes.get(key).unwrap()))
                    && lhs_additional_attributes == rhs_additional_attributes
            } else {
                false
            }
        }
        // Sets are equivalent if their elements are equivalent
        (
            TypeVariant::Set {
                element: lhs_element,
            },
            TypeVariant::Set {
                element: rhs_element,
            },
        ) => shape_equiv(lhs_element.as_ref(), rhs_element.as_ref()),

        // Base types are equivalent to `EntityOrCommon` variants where the type_name is of the
        // form `__cedar::<base type>`
        (TypeVariant::String, TypeVariant::EntityOrCommon { type_name })
        | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::String) => {
            is_internal_type(type_name, "String")
        }
        (TypeVariant::Long, TypeVariant::EntityOrCommon { type_name })
        | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::Long) => {
            is_internal_type(type_name, "Long")
        }
        (TypeVariant::Boolean, TypeVariant::EntityOrCommon { type_name })
        | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::Boolean) => {
            is_internal_type(type_name, "Bool")
        }
        (TypeVariant::Extension { name }, TypeVariant::EntityOrCommon { type_name })
        | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::Extension { name }) => {
            is_internal_type(type_name, &name.to_string())
        }

        (TypeVariant::Entity { name }, TypeVariant::EntityOrCommon { type_name })
        | (TypeVariant::EntityOrCommon { type_name }, TypeVariant::Entity { name }) => {
            type_name == name
        }

        // Types that are exactly equal are of course equivalent
        (lhs, rhs) => lhs == rhs,
    }
}

/// Attributes are equivalent iff their shape is equivalent and they have the same required status
fn attribute_equiv<N: TypeName + Clone + PartialEq>(
    lhs: &TypeOfAttribute<N>,
    rhs: &TypeOfAttribute<N>,
) -> bool {
    lhs.required == rhs.required && shape_equiv(&lhs.ty, &rhs.ty)
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
    lhs: json_schema::ActionType<N>,
    rhs: json_schema::ActionType<N>,
) -> Result<(), String> {
    if lhs.attributes != rhs.attributes {
        Err(format!("Attributes don't match for `{name}`"))
    } else if lhs.member_of != rhs.member_of {
        Err(format!("Member of don't match for `{name}`"))
    } else {
        match (lhs.applies_to, rhs.applies_to) {
            (None, None) => Ok(()),
            (Some(lhs), Some(rhs)) => {
                // If either of them has at least one empty appliesTo list, the other must have the same attribute.
                if (either_empty(&lhs) && either_empty(&rhs)) || apply_spec_equiv(&lhs, &rhs) {
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
            (Some(applies_to), None) | (None, Some(applies_to)) if either_empty(&applies_to) => {
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

/// ApplySpecs are equivalent iff
/// A) the principal and resource type lists are equal
/// B) the context shapes are equivalent
fn apply_spec_equiv<N: TypeName + Clone + PartialEq + Ord>(
    lhs: &ApplySpec<N>,
    rhs: &ApplySpec<N>,
) -> bool {
    shape_equiv(&lhs.context.0, &rhs.context.0)
        && vector_equiv(&lhs.principal_types, &rhs.principal_types)
        && vector_equiv(&lhs.resource_types, &rhs.resource_types)
}

fn either_empty<N>(spec: &json_schema::ApplySpec<N>) -> bool {
    spec.principal_types.is_empty() || spec.resource_types.is_empty()
}

/// Just compare entity attribute types and context types are equivalent
pub fn validator_schema_attr_types_equivalent(
    schema1: &cedar_policy_validator::ValidatorSchema,
    schema2: &cedar_policy_validator::ValidatorSchema,
) -> bool {
    let entity_attr_tys1: HashMap<
        &cedar_drt::ast::EntityType,
        HashMap<&smol_str::SmolStr, &cedar_policy_validator::types::AttributeType>,
    > = HashMap::from_iter(
        schema1
            .entity_types()
            .map(|(name, ty)| (name, HashMap::from_iter(ty.attributes()))),
    );
    let entity_attr_tys2 = HashMap::from_iter(
        schema2
            .entity_types()
            .map(|(name, ty)| (name, HashMap::from_iter(ty.attributes()))),
    );
    let context_ty1: HashSet<&cedar_policy_validator::types::Type> = HashSet::from_iter(
        schema1
            .action_entities()
            .unwrap()
            .iter()
            .map(|e| schema1.get_action_id(e.uid()).unwrap().context_type()),
    );
    let context_ty2: HashSet<&cedar_policy_validator::types::Type> = HashSet::from_iter(
        schema2
            .action_entities()
            .unwrap()
            .iter()
            .map(|e| schema1.get_action_id(e.uid()).unwrap().context_type()),
    );
    entity_attr_tys1 == entity_attr_tys2 && context_ty1 == context_ty2
}
