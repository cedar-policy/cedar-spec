/*
 * Copyright Cedar Contributors. All Rights Reserved.
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
use cedar_policy_core::parser::err::{ParseError, ToASTErrorKind};
use cedar_policy_core::parser::parse_policyset;

fuzz_target!(|input: String| {
    // Ensure the parser does not crash
    #[allow(clippy::single_match)]
    match parse_policyset(&input) {
        Ok(_) => (),
        Err(errs) => {
            // Also check that we don't see a few specific errors.
            // `AnnotationInvariantViolation` and `MembershipInvariantViolation`
            // are documented as only being returned for internal invariant violations.  It's not
            // entirely clear when `MissingNodeData` might be returned, but I don't believe it
            // should be possible, and, practically, it doesn't make this target fail.
            assert!(
                !errs.0.iter().any(|e| matches!(
                e,
                ParseError::ToAST(e) if matches!(e.kind(),
                    ToASTErrorKind::AnnotationInvariantViolation
                        | ToASTErrorKind::MembershipInvariantViolation
                        | ToASTErrorKind::MissingNodeData)
                )),
                "{:?}",
                errs
            )
        }
    };
});
