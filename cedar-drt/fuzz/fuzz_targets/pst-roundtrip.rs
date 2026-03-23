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
use cedar_drt_inner::{fuzz_target, pst_equiv};

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
        Err(e) => panic!("AST → PST #1 failed: {:?}", e),
    };
    assert_eq!(
        ast_template.id().clone().into_smolstr(),
        pst1.id.0,
        "AST -> PST ids"
    );
    // PST → AST → PST (roundtrip through AST)
    let ast2: ast::Template = match pst1.clone().try_into() {
        Ok(t) => t,
        Err(e) => panic!("PST → AST #1 failed: {:?}\nPST: {:?}", e, pst1),
    };
    assert_eq!(ast_template.id(), ast2.id(), "IDs");
    let pst2: pst::Template = match ast2.try_into() {
        Ok(t) => t,
        Err(e) => panic!("AST → PST (second) failed: {:?}\nPST1: {:?}", e, pst1),
    };

    // pst1 and pst2
    pst_equiv::check_template_equivalence(
        &pst1,
        &pst2,
        pst_equiv::CheckingParams { check_ids: true },
    );
});
