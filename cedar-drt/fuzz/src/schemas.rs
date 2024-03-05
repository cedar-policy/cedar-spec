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
    if lhs.0.len() == rhs.0.len() {
        lhs.0
            .into_iter()
            .map(|(name, lhs_namespace)| {
                let rhs_namespace = rhs
                    .0
                    .get(&name)
                    .ok_or_else(|| format!("`{name}` does not exist in RHS schema"))?;
                namespace_equivalence(lhs_namespace, rhs_namespace.clone())
            })
            .fold(Ok(()), Result::and)
    } else {
        Err("schema differ in number of namespaces".to_string())
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
            (Some(lhs), Some(rhs)) if is_either_empty(&lhs) => {
                if is_either_empty(&rhs) {
                    Ok(())
                } else {
                    Err(format!(
                        "Mismatched applies to in `{name}`. lhs : `{:?}`,rhs: `{:?}`",
                        lhs, rhs
                    ))
                }
            }
            (Some(lhs), Some(rhs)) if is_either_empty(&rhs) => {
                if is_either_empty(&lhs) {
                    Ok(())
                } else {
                    Err(format!(
                        "Mismatched applies to in `{name}`. lhs : `{:?}`,rhs: `{:?}`",
                        lhs, rhs
                    ))
                }
            }
            // if neither is non-applicable, they must be equal
            (Some(lhs), Some(rhs)) => {
                if rhs == lhs {
                    Ok(())
                } else {
                    Err(format!(
                        "Mismatched applies to in `{name}`. lhs : `{:?}`,rhs: `{:?}`",
                        lhs, rhs
                    ))
                }
            }
            // if one of them has `appliesTo` being null, then the other must have both principal and resource types unspecified
            (Some(spec), None) | (None, Some(spec)) if is_both_unspecified(&spec) => Ok(()),
            (Some(_), None) => Err(format!(
                "Mismatched applies to in `{name}`, lhs was `Some`, `rhs` was `None`"
            )),
            (None, Some(_)) => Err(format!(
                "Mismatched applies to in `{name}`, lhs was `None`, `rhs` was `Some`"
            )),
        }
    }
}

fn is_both_unspecified(spec: &ApplySpec) -> bool {
    spec.resource_types.is_none() && spec.principal_types.is_none()
}

fn is_either_empty(spec: &ApplySpec) -> bool {
    matches!(spec.resource_types.as_ref(), Some(ts) if ts.is_empty())
        || matches!(spec.principal_types.as_ref(), Some(ts) if ts.is_empty())
}
