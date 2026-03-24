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

#![no_main]

use cedar_drt::{check_policy_equivalence, logger::initialize_log};
use cedar_drt_inner::{fuzz_target, pst_equiv, pst_gen::FuzzTargetInput};

use cedar_policy_core::ast;
use cedar_policy_core::pst;
use log::debug;

// PST → AST → PST → AST → PST roundtrip
// PST → AST is lossy (desugars >=, >, !=), so we go through AST twice
// and check that it stabilizes after one normalization pass.
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let template = input.template;

    debug!("Running PST→AST→PST→AST→PST roundtrip on: {:?}", template);

    let ast1: ast::Template = template
        .clone()
        .try_into()
        .unwrap_or_else(|e| panic!("PST → AST #1 failed: {:?}", e));

    let pst2: pst::Template = ast1
        .clone()
        .try_into()
        .unwrap_or_else(|e| panic!("AST #1 → PST #2 failed: {:?}", e));

    let ast2: ast::Template = pst2
        .clone()
        .try_into()
        .unwrap_or_else(|e| panic!("PST #2 → AST #2 failed: {:?}\nPST #2: {:?}", e, pst2));

    let pst3: pst::Template = ast2
        .clone()
        .try_into()
        .unwrap_or_else(|e| panic!("AST #2 → PST #3 failed: {:?}", e));

    // AST equivalence: ast1 == ast2
    check_policy_equivalence(&ast1, &ast2);

    // PST equivalence after stabilization: pst2 == pst3
    pst_equiv::check_template_equivalence(
        &pst2,
        &pst3,
        pst_equiv::CheckingParams { check_ids: true },
    );
});
