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

use cedar_policy_core::ast::{
    ActionConstraint, AnyId, Effect, Expr, PolicySet, PrincipalConstraint, ResourceConstraint,
    Template,
};
use cedar_policy_core::parser::err::{ParseError, ParseErrors, ToASTErrorKind};
use smol_str::SmolStr;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};

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

// Check that we don't see a few specific errors, which correspond to violations
// of internal invariants.
pub fn check_for_internal_errors(errs: ParseErrors) {
    assert!(
        !errs.iter().any(|e| matches!(
        e,
        ParseError::ToAST(e) if matches!(e.kind(),
            ToASTErrorKind::MembershipInvariantViolation
                | ToASTErrorKind::EmptyNodeInvariantViolation)
        )),
        "Parse errors included unexpected internal errors: {:?}",
        miette::Report::new(errs).wrap_err("unexpected internal error")
    )
}

// Represents the aspects of a template that are preserved through conversions
// to different representations.
#[derive(Eq, Debug)]
struct PreservedTemplate<'a> {
    effect: Effect,
    principal_constraint: &'a PrincipalConstraint,
    action_constraint: &'a ActionConstraint,
    resource_constraint: &'a ResourceConstraint,
    annotations: BTreeMap<&'a AnyId, &'a SmolStr>,
    non_scope_constraints: &'a Expr,
}

impl<'a> PartialEq for PreservedTemplate<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.effect == other.effect
            && self.principal_constraint == other.principal_constraint
            && self.action_constraint == other.action_constraint
            && self.resource_constraint == other.resource_constraint
            && self.annotations == other.annotations
            && self
                .non_scope_constraints
                .eq_shape(other.non_scope_constraints)
    }
}

impl<'a> Hash for PreservedTemplate<'a> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.effect.hash(hasher);
        self.principal_constraint.hash(hasher);
        self.action_constraint.hash(hasher);
        self.resource_constraint.hash(hasher);
        self.annotations.hash(hasher);
        self.non_scope_constraints.hash_shape(hasher);
    }
}

impl<'a> From<&'a Template> for PreservedTemplate<'a> {
    fn from(value: &'a Template) -> Self {
        PreservedTemplate {
            effect: value.effect(),
            principal_constraint: value.principal_constraint(),
            action_constraint: value.action_constraint(),
            resource_constraint: value.resource_constraint(),
            annotations: value.annotations().map(|(k, v)| (k, &v.val)).collect(),
            non_scope_constraints: value.non_scope_constraints(),
        }
    }
}

// Checks that the static policies and templates in the specified
// sets are equivalent, ignoring policy ids and source locations.
// Panics if the two sets are not equivalent.
pub fn check_policy_set_equivalence(set1: &PolicySet, set2: &PolicySet) {
    // Convert templates in each set to preserved templates
    let t1 = set1
        .all_templates()
        .map(PreservedTemplate::from)
        .collect::<HashSet<PreservedTemplate>>();
    let t2 = set2
        .all_templates()
        .map(PreservedTemplate::from)
        .collect::<HashSet<PreservedTemplate>>();
    // Check that the sets are the same size
    assert_eq!(t1, t2);
}
