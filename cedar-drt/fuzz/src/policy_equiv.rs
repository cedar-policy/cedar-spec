use cedar_policy_core::ast::{AnyId, Template};
use smol_str::SmolStr;
use std::collections::HashMap;

// Check that two policies are equivalent, ignoring policy ids and source
// locations.  Panic if the two policies are not the same.
pub fn check_policy_equivalence(p_old: &Template, p_new: &Template) {
    // just dump to standard hashmaps to check equality without order.
    // also ignore source locations, which are not preserved in general
    let new_anno: HashMap<&AnyId, &SmolStr> =
        p_new.annotations().map(|(k, v)| (k, &v.val)).collect();
    let old_anno: HashMap<&AnyId, &SmolStr> =
        p_old.annotations().map(|(k, v)| (k, &v.val)).collect();
    similar_asserts::assert_eq!(new_anno, old_anno);
    similar_asserts::assert_eq!(p_new.effect(), p_old.effect());
    similar_asserts::assert_eq!(p_new.principal_constraint(), p_old.principal_constraint(),);
    similar_asserts::assert_eq!(p_new.action_constraint(), p_old.action_constraint(),);
    similar_asserts::assert_eq!(p_new.resource_constraint(), p_old.resource_constraint(),);
    assert!(
        p_new
            .non_scope_constraints()
            .eq_shape(p_old.non_scope_constraints()),
        "{}",
        similar_asserts::SimpleDiff::from_str(
            &p_new.non_scope_constraints().to_string(),
            &p_old.non_scope_constraints().to_string(),
            "new",
            "old"
        )
    );
}
