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

use cedar_policy_core::pst;
use cedar_policy_generators::hierarchy::HierarchyGenerator;
use cedar_policy_generators::pst::{
    arbitrary_pst_policy_set, arbitrary_pst_policy_set_size_hint, arbitrary_pst_template,
    arbitrary_pst_template_size_hint,
};
use cedar_policy_generators::schema::Schema;
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_generators::settings::ABACSettings;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Fuzz target input: a PST template generated from a schema/hierarchy.
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    pub template: pst::Template,
}

/// Fuzz target input: a PST policy set generated from a schema/hierarchy.
#[derive(Debug, Clone)]
pub struct PolicySetFuzzTargetInput {
    pub policy_set: pst::PolicySet,
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
        let template = arbitrary_pst_template(&hierarchy, 5, 5, u)?;
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

impl<'a> Arbitrary<'a> for PolicySetFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy_set = arbitrary_pst_policy_set(&hierarchy, 5, 5, u)?;
        Ok(Self { policy_set })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            arbitrary_pst_policy_set_size_hint(depth),
        ]))
    }
}
