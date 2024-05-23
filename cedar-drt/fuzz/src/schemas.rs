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

use std::collections::{HashMap, HashSet};

use cedar_policy_validator::{ActionType, ApplySpec, NamespaceDefinition, SchemaFragment};

/// Check if two schema fragments are equivalent, modulo empty apply specs.
/// We do this because there are schemas that are representable in the JSON that are not
/// representable in the human-readable syntax. All of these non-representable schemas
/// are equivalent to one that is representable.
///
/// Example:
/// You can have a JSON schema with an action that has no applicable principals and some applicable
/// resources.
/// In the human-readable syntax, you can't. The only way to write an action with no applicable
/// principals is:
/// ```cedarschema
/// action a;
/// ```
/// Specifying an action with no applicable principals and no applicable resources.
///
/// However, this is _equivalent_. An action that can't be applied to any principals can't ever be
/// used. Whether or not there are applicable resources is useless.
///
pub fn equivalence_check(lhs: SchemaFragment, rhs: SchemaFragment) -> Result<(), String> {
    // We need to special-case two schemas both being trivial because both `{}`
    // and `{"": {"entityTypes": {}, "actions": {}}}` translate to empty strings
    // in the human-readable schema format
    if is_trivial(&lhs) && is_trivial(&rhs) {
        Ok(())
    } else if lhs.0.len() == rhs.0.len() {
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

// A schema fragment is trivial if it is empty or it's the empty namespace with
// all declarations being empty
fn is_trivial(schema: &SchemaFragment) -> bool {
    if schema.0.len() == 0 {
        true
    } else if let Some(def) = schema.0.get(&None) {
        def.entity_types.is_empty() && def.common_types.is_empty() && def.common_types.is_empty()
    } else {
        false
    }
}

fn namespace_equivalence(lhs: NamespaceDefinition, rhs: NamespaceDefinition) -> Result<(), String> {
    if lhs.common_types != rhs.common_types {
        Err("Common types differ".to_string())
    } else if lhs.entity_types != rhs.entity_types {
        Err("Entity types differ".to_string())
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

fn action_type_equivalence(name: &str, lhs: ActionType, rhs: ActionType) -> Result<(), String> {
    if lhs.attributes != rhs.attributes {
        Err(format!("Attributes don't match for `{name}`"))
    } else if lhs.member_of != rhs.member_of {
        Err(format!("Member of don't match for `{name}`"))
    } else {
        match (lhs.applies_to, rhs.applies_to) {
            (None, None) => Ok(()),
            (Some(lhs), Some(rhs)) => {
                // If either of them has at least one empty appliesTo list, the other must have the same attribute.
                // Otherwise both of them must apply to unspecified entities or non-empty entity lists, which must be equal.
                if (either_empty(&lhs) && either_empty(&rhs)) || rhs == lhs {
                    Ok(())
                } else {
                    Err(format!(
                        "Mismatched applies to in `{name}`. lhs : `{:?}`,rhs: `{:?}`",
                        lhs, rhs
                    ))
                }
            }
            // if one of them has `appliesTo` being null, then the other must have both principal and resource types unspecified
            (Some(spec), None) | (None, Some(spec)) if both_unspecified(&spec) => Ok(()),
            (Some(_), None) => Err(format!(
                "Mismatched applies to in `{name}`, lhs was `Some`, `rhs` was `None`"
            )),
            (None, Some(_)) => Err(format!(
                "Mismatched applies to in `{name}`, lhs was `None`, `rhs` was `Some`"
            )),
        }
    }
}

fn both_unspecified(spec: &ApplySpec) -> bool {
    spec.resource_types.is_none() && spec.principal_types.is_none()
}

fn either_empty(spec: &ApplySpec) -> bool {
    matches!(spec.resource_types.as_ref(), Some(ts) if ts.is_empty())
        || matches!(spec.principal_types.as_ref(), Some(ts) if ts.is_empty())
}

/// Just compare entity attribute types and context types are equivalent
pub fn validator_schema_attr_types_equivalent(
    schema1: &cedar_policy_validator::ValidatorSchema,
    schema2: &cedar_policy_validator::ValidatorSchema,
) -> bool {
    let entity_attr_tys1: HashMap<
        &cedar_drt::ast::Name,
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
    let context_ty1: HashSet<cedar_policy_validator::types::Type> = HashSet::from_iter(
        schema1
            .action_entities()
            .unwrap()
            .iter()
            .map(|e| schema1.get_action_id(e.uid()).unwrap().context_type()),
    );
    let context_ty2: HashSet<cedar_policy_validator::types::Type> = HashSet::from_iter(
        schema2
            .action_entities()
            .unwrap()
            .iter()
            .map(|e| schema1.get_action_id(e.uid()).unwrap().context_type()),
    );
    entity_attr_tys1 == entity_attr_tys2 && context_ty1 == context_ty2
}
