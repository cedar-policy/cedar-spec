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

use cedar_policy_core::ast::{AnyId, PolicySet, Template};
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

// Exposes only the aspects of a template that are preserved through conversions
// to different representations.
#[derive(Eq, Debug)]
struct PreservedTemplate<'a> {
    template: &'a Template,
    annotations: BTreeMap<&'a AnyId, &'a SmolStr>,
}

impl<'a> PartialEq for PreservedTemplate<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.template.effect() == other.template.effect()
            && self.template.principal_constraint() == other.template.principal_constraint()
            && self.template.action_constraint() == other.template.action_constraint()
            && self.template.resource_constraint() == other.template.resource_constraint()
            && self.annotations == other.annotations
            && self
                .template
                .non_scope_constraints()
                .eq_shape(other.template.non_scope_constraints())
    }
}

impl<'a> Hash for PreservedTemplate<'a> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.template.effect().hash(hasher);
        self.template.principal_constraint().hash(hasher);
        self.template.action_constraint().hash(hasher);
        self.template.resource_constraint().hash(hasher);
        self.template.non_scope_constraints().hash_shape(hasher);
        self.annotations.hash(hasher);
    }
}

impl<'a> From<&'a Template> for PreservedTemplate<'a> {
    fn from(value: &'a Template) -> Self {
        PreservedTemplate {
            template: value,
            annotations: value.annotations().map(|(k, v)| (k, &v.val)).collect(),
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
