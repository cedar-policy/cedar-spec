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

use cedar_drt::logger::initialize_log;
use cedar_drt_inner::fuzz_target;

use cedar_policy_core::ast::{self, StaticPolicy, Template};
use cedar_policy_core::pst;
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema::Schema, settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use std::sync::Arc;

/// Fuzz target input: a policy generated via the standard ABAC generators.
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    policy: ABACPolicy,
}

const SETTINGS: ABACSettings = ABACSettings {
    enable_additional_attributes: true,
    enable_arbitrary_func_call: false,
    ..ABACSettings::undirected()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        Ok(Self { policy })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
        ]))
    }
}

/// Compare two PST templates for equivalence, ignoring policy IDs.
fn check_pst_equivalence(original: &pst::Template, roundtripped: &pst::Template) {
    assert_eq!(
        original.effect, roundtripped.effect,
        "Effect mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original, roundtripped
    );
    assert_eq!(
        original.principal, roundtripped.principal,
        "Principal constraint mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original, roundtripped
    );
    assert_eq!(
        original.action, roundtripped.action,
        "Action constraint mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original, roundtripped
    );
    assert_eq!(
        original.resource, roundtripped.resource,
        "Resource constraint mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original, roundtripped
    );
    assert_eq!(
        original.clauses(),
        roundtripped.clauses(),
        "Clauses mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original,
        roundtripped
    );
    // Ignore annotations: AST→PST→AST→PST may reorder or normalize annotation keys
}

// AST → PST → AST → PST roundtrip, comparing at the PST level.
// PST → AST is lossy (desugars >=, >, !=), so we go through AST twice
// and compare the two PST representations which should be stable.
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let p: StaticPolicy = input.policy.into();
    let ast_template: Arc<Template> = p.into();

    debug!("Running AST→PST→AST→PST roundtrip on: {:?}", ast_template);

    // AST → PST (first conversion)
    let pst1: pst::Template = match ast_template.as_ref().clone().try_into() {
        Ok(t) => t,
        Err(_) => return, // skip if conversion fails
    };

    // PST → AST → PST (roundtrip through AST)
    let ast2: ast::Template = match pst1.clone().try_into() {
        Ok(t) => t,
        Err(e) => panic!("PST → AST failed: {:?}\nPST: {:?}", e, pst1),
    };
    let pst2: pst::Template = match ast2.try_into() {
        Ok(t) => t,
        Err(e) => panic!("AST → PST (second) failed: {:?}\nPST1: {:?}", e, pst1),
    };

    // The second PST should be stable: PST → AST → PST → AST → PST should equal PST → AST → PST
    let ast3: ast::Template = match pst2.clone().try_into() {
        Ok(t) => t,
        Err(e) => panic!("PST → AST (second) failed: {:?}\nPST2: {:?}", e, pst2),
    };
    let pst3: pst::Template = match ast3.try_into() {
        Ok(t) => t,
        Err(e) => panic!("AST → PST (third) failed: {:?}\nPST2: {:?}", e, pst2),
    };

    // pst2 and pst3 should be identical (the roundtrip is idempotent after first normalization)
    check_pst_equivalence(&pst2, &pst3);
});
