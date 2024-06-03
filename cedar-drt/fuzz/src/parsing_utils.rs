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

use cedar_policy_core::ast::{AnyId, Template};
use cedar_policy_core::parser::err::{ParseError, ParseErrors, ToASTErrorKind};
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

// Check that we don't see a few specific errors, which correspond to violations
// of internal invariants.
pub fn check_for_internal_errors(errs: ParseErrors) {
    assert!(
        !errs.iter().any(|e| matches!(
        e,
        ParseError::ToAST(e) if matches!(e.kind(),
            ToASTErrorKind::AnnotationInvariantViolation
                | ToASTErrorKind::MembershipInvariantViolation
                | ToASTErrorKind::EmptyNodeInvariantViolation)
        )),
        "Parse errors included unexpected internal errors: {:?}",
        miette::Report::new(errs).wrap_err("unexpected internal error")
    )
}
