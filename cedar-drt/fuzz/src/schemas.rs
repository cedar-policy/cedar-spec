use cedar_policy_validator::{ActionType, ApplySpec, NamespaceDefinition, SchemaFragment};

/// Check if two schema fragments are equivalent
pub fn semantic_equality_check(lhs: SchemaFragment, rhs: SchemaFragment) -> Result<(), String> {
    if lhs.0.len() == rhs.0.len() {
        lhs.0
            .into_iter()
            .map(|(name, lhs_namespace)| {
                let rhs_namespace = rhs
                    .0
                    .get(&name)
                    .ok_or_else(|| format!("`{name}` does not exist in RHS schema"))?;
                semantic_namespace_equality(lhs_namespace, rhs_namespace.clone())
            })
            .fold(Ok(()), result_combiner)
    } else {
        Err("schema differ in number of namespaces".to_string())
    }
}

fn semantic_namespace_equality(
    lhs: NamespaceDefinition,
    rhs: NamespaceDefinition,
) -> Result<(), String> {
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
                semantic_action_type_equality(name.as_ref(), lhs_action, rhs_action.clone())
            })
            .fold(Ok(()), result_combiner)
    }
}

fn semantic_action_type_equality(
    name: &str,
    lhs: ActionType,
    rhs: ActionType,
) -> Result<(), String> {
    if lhs.attributes != rhs.attributes {
        Err(format!("Attributes don't match for `{name}`"))
    } else if lhs.member_of != rhs.member_of {
        Err(format!("Member of don't match for `{name}`"))
    } else {
        match (lhs.applies_to, rhs.applies_to) {
            (None, None) => Ok(()),
            (Some(lhs), Some(rhs)) => {
                if empty_target(&rhs) || empty_target(&lhs) || rhs == lhs {
                    Ok(())
                } else {
                    Err(format!(
                        "Mismatched applies to in `{name}`. lhs : `{:?}`,rhs: `{:?}`",
                        lhs, rhs
                    ))
                }
            }
            (Some(spec), None) | (None, Some(spec)) if empty_target(&spec) => Ok(()),
            (Some(_), None) => Err(format!(
                "Mismatched applies to in `{name}`, lhs was `Some`, `rhs` was `None`"
            )),
            (None, Some(_)) => Err(format!(
                "Mismatched applies to in `{name}`, lhs was `None`, `rhs` was `Some`"
            )),
        }
    }
}

fn empty_target(spec: &ApplySpec) -> bool {
    spec.resource_types
        .as_ref()
        .map(|v| v.is_empty())
        .unwrap_or(false)
        || spec
            .principal_types
            .as_ref()
            .map(|v| v.is_empty())
            .unwrap_or(false)
}

fn result_combiner<E>(lhs: Result<(), E>, rhs: Result<(), E>) -> Result<(), E> {
    match (lhs, rhs) {
        (Err(e), _) | (_, Err(e)) => Err(e),
        _ => Ok(()),
    }
}
