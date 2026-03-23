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

use cedar_policy_core::est;
use cedar_policy_core::pst;
use cedar_policy_generators::hierarchy::HierarchyGenerator;
use cedar_policy_generators::pst::{arbitrary_pst_template, arbitrary_pst_template_size_hint};
use cedar_policy_generators::schema::Schema;
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_generators::settings::ABACSettings;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;

/// Fuzz target input: a PST template generated from a schema/hierarchy.
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    template: pst::Template,
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
        let template = arbitrary_pst_template(&hierarchy, 3, 3, u)?;
        Ok(Self { template })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            arbitrary_pst_template_size_hint(depth),
        ]))
    }
}

// PST → EST → PST roundtrip
fn round_trip_pst_est(template: &pst::Template) -> pst::Template {
    let est_policy: est::Policy = template
        .clone()
        .try_into()
        .unwrap_or_else(|e| panic!("PST → EST failed: {:?}\nTemplate: {:?}", e, template));

    let roundtripped: pst::Template = est_policy
        .try_into()
        .unwrap_or_else(|e| panic!("EST → PST failed: {:?}\nOriginal: {:?}", e, template));

    roundtripped
}

fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let template = input.template;

    debug!("Running PST→EST→PST roundtrip on: {:?}", template);

    let roundtripped = round_trip_pst_est(&template);
    // Check PST equivalence, not including IDs because they get lost in the EST
    pst_equiv::check_template_equivalence(
        &template,
        &roundtripped,
        pst_equiv::CheckingParams { check_ids: false },
    );
});
