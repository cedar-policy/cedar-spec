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

use cedar_drt::ast::PolicyID;
use cedar_drt::extensions::Extensions;
use cedar_drt::{est, parser, ValidatorSchema};
use cedar_policy::SchemaFragment;
use cedar_policy_core::ast::{AnyId, Template};
use cedar_policy_core::parser::err::{ParseError, ParseErrors, ToASTErrorKind};
use smol_str::SmolStr;
use std::collections::HashMap;
use thiserror::Error;

#[derive(miette::Diagnostic, Error, Debug)]
enum ESTParseError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    CSTToEST(#[from] parser::err::ParseErrors),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ESTToAST(#[from] est::FromJsonError),
}

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
            ToASTErrorKind::MembershipInvariantViolation)
                // | ToASTErrorKind::EmptyNodeInvariantViolation)
        )),
        "Parse errors included unexpected internal errors: {:?}",
        miette::Report::new(errs).wrap_err("unexpected internal error")
    )
}

// Panic if historical bugs are detected.
pub fn check_policy_est_parse_bugs(policy: &est::Policy) {
    // Issue 994: Check if JSON policy defines an annotation with a space
    if let Ok(issue_388) = std::env::var("ISSUE_388") {
        // Get the annotations value from the policy JSON
        if let Ok(ast_from_est) = policy
            .clone()
            .try_into_ast_template(Some(PolicyID::from_string("policy0")))
            .map_err(ESTParseError::from)
        {
            let ast_from_cedar =
                cedar_policy_core::parser::parse_policy_template(None, &ast_from_est.to_string());

            match ast_from_cedar {
                Ok(ast_from_cedar) => {
                    check_policy_equivalence(&ast_from_est, &ast_from_cedar);
                }

                Err(e) => {
                    println!("{:?}", miette::Report::new(e));
                    panic!("Policy parsed from est to ast but did not roundtrip ast->text->ast");
                }
            }
        }
    } else if let Ok(issue_994) = std::env::var("ISSUE_994") {
        // Get the annotations value from the policy JSON
        for (_, annotation) in policy.clone().annotations {
            if annotation.contains(' ') {
                panic!("Found issue 994!");
            }
        }
    } else if let Ok(issue_925) = std::env::var("ISSUE_925") {
        let policy_ast = policy.clone().try_into_ast_policy(None);
        if let Err(e) = policy_ast {
            match e {
                cedar_policy_core::est::FromJsonError::InvalidActionType(_) => {
                    assert!(false, "Found issue 925!");
                }
                _ => (),
            }
        }
    } else if let Ok(issue_891) = std::env::var("ISSUE_891") {
        let policy_ast = policy.clone().try_into_ast_policy(None);
        if let Err(e) = policy_ast {
            match e {
                cedar_policy_core::est::FromJsonError::UnknownExtensionFunction(_) => {
                    assert!(false, "Found issue 891!");
                }
                _ => (),
            }
        }
    } else if let Ok(issue_606) = std::env::var("ISSUE_606") {
        let policy_ast = policy.clone().try_into_ast_policy(None);
        if let Err(e) = policy_ast {
            match e {
                cedar_policy_core::est::FromJsonError::SlotsInConditionClause(_) => {
                    assert!(false, "Found issue 626!");
                }
                _ => (),
            }
        }
    }
}

pub fn check_policy_cedar_parse_bugs(policy: String) {
    if let Ok(issue_618) = std::env::var("ISSUE_618") {
        // TODO: check issue 618
    }
}

// // Panic if historical bugs are detected.
// pub fn check_schema_parse_bugs(schema: &SchemaFragment) {
//     if let Ok(issue_875) = std::env::var("ISSUE_875") {
//         // TODO: check issue 875
//         let schema_json = schema.clone().to_json_value().unwrap();
//         let schema = ValidatorSchema::from_json_value(schema_json, Extensions::all_available());
//         // Check that result contains SchemaError with "unknown extension type"
//         match schema {
//             Err(cedar_policy_validator::SchemaError::UnknownExtensionType(_)) => {
//                 panic!("Found issue 875!");
//             }
//             _ => (),
//         }
//     }
// }
