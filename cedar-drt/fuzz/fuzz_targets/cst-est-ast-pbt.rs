/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#![no_main]

use cedar_drt_inner::fuzz_target;

use cedar_policy_core::parser::err::ParseError;
use cedar_policy_core::parser::err::ParseErrors;
use cedar_policy_core::parser::err::ToASTErrorKind;

fn assert_not_invariant_violation(errs: &ParseErrors) {
    for e in errs {
        assert!(
            !matches!(
            e,
            ParseError::ToAST(e) if matches!(e.kind(),
                ToASTErrorKind::AnnotationInvariantViolation
                    | ToASTErrorKind::MembershipInvariantViolation
                    | ToASTErrorKind::MissingNodeData)
            ),
            "{e:?}",
        )
    }
}

// Given a CST
// * If it converts to and AST, then it converts to an EST which itself
//   converts to an AST.  These ASTs are equivalent.
// * If c does not convert to an AST, then it either does not convert to an
//   EST or, if it converts to and EST, the EST does not convert to an AST.

fuzz_target!(|cst: cedar_policy_core::parser::Node<
    Option<cedar_policy_core::parser::cst::Policy>,
>| {
    println!("{}", cst.node.clone().unwrap());
    let mut errs = cedar_policy_core::parser::err::ParseErrors::new();
    let cst_ast =
        cst.to_policy_template(cedar_policy_core::ast::PolicyID::from_string(""), &mut errs);
    assert_not_invariant_violation(&errs);

    let est_ast = cst
        .into_inner()
        .0
        .unwrap()
        .try_into()
        .map_err(|e: ParseErrors| format!("cst->est: {e}"))
        .and_then(|est: cedar_policy_core::est::Policy| {
            est.try_into_ast_template(Some(cedar_policy_core::ast::PolicyID::from_string("")))
                .map_err(|e| format!("est->ast: {e}"))
        });

    match (cst_ast, est_ast) {
        (Some(cst_ast),  Ok(est_ast)) => {
            assert_eq!(
                cst_ast.slots().collect::<Vec<_>>(),
                est_ast.slots().collect::<Vec<_>>(),
            );
            assert_eq!(
                cst_ast.annotations().collect::<Vec<_>>(),
                est_ast.annotations().collect::<Vec<_>>(),
            );
            assert_eq!(
                cst_ast.effect(),
                est_ast.effect(),
            );
            assert_eq!(
                cst_ast.principal_constraint(),
                est_ast.principal_constraint(),
            );
            assert_eq!(
                cst_ast.action_constraint(),
                est_ast.action_constraint(),
            );
            assert_eq!(
                cst_ast.resource_constraint(),
                est_ast.resource_constraint(),
            );
            // This could turn out to be be too strong of a condition. There are
            // plenty of equivalent expression in Cedar, so they may be
            // constructed slightly differently. If that it's easy to fix things
            // to get an exact match, then I'd suggest doing that rather than
            // adjusting relaxing this assertion.
            assert!(
                cst_ast.non_head_constraints().eq_shape(est_ast.non_head_constraints()),
                "cst_ast condition: {}\nest_ast condition: {}\n",
                cst_ast.non_head_constraints(),
                est_ast.non_head_constraints()
            );
        }
        (None, Err(_)) => (),
        (Some(cst_ast), Err(est_err)) => panic!("Parsed directly to ast, but not via est\ncst->ast: {cst_ast}\ncst->est->ast: {est_err}"),
        (None, Ok(est_ast)) => panic!("Did not parse directly to ast, but did via est\ncst->ast: {errs}\ncst->est->ast: {est_ast}"),
        _ => (),
    }
});
