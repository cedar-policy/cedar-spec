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

use arbitrary::{self, Arbitrary, Unstructured};
use bolero::check;
use cedar_bolero_fuzz::{
    drop_some_entities, dump_fuzz_test_case, run_eval_test, FuzzTestCase, TestCaseFormat,
};
use cedar_drt::utils::expr_to_est;
use cedar_drt::*;
use cedar_policy::Request;
use cedar_policy_core::{ast::Expr, entities::Entities};
use cedar_policy_generators::abac::ABACRequest;
use cedar_policy_generators::err::Error;
use cedar_policy_generators::hierarchy::{self, Hierarchy, HierarchyGenerator};
use cedar_policy_generators::schema::{arbitrary_schematype_with_bounded_depth, Schema};
use cedar_policy_generators::settings::ABACSettings;
use log::debug;
use serde::Serialize;
use serde_json::{json, Value};
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone, Serialize)]
pub struct FuzzTargetInput {
    /// generated schema
    #[serde(skip)]
    pub schema: Schema,
    // generated entity slice
    #[serde(skip)]
    pub entities: Entities,
    /// generated expression
    #[serde(serialize_with = "expr_to_est")]
    pub expression: Expr,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    #[serde(skip)]
    pub request: ABACRequest,
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let toplevel_type = arbitrary_schematype_with_bounded_depth(
            &SETTINGS,
            schema.entity_types(),
            SETTINGS.max_depth,
            u,
        )?;
        let expr_gen = schema.exprgenerator(Some(&hierarchy));
        let expression =
            expr_gen.generate_expr_for_schematype(&toplevel_type, SETTINGS.max_depth, u)?;

        let request = schema.arbitrary_request(&hierarchy, u)?;
        let all_entities = Entities::try_from(hierarchy).map_err(Error::EntitiesError)?;
        let entities = drop_some_entities(all_entities, u)?;
        Ok(Self {
            schema,
            entities,
            expression,
            request,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
        ])
    }
}

impl TestCaseFormat for FuzzTargetInput {
    fn to_fuzz_test_case(&self) -> FuzzTestCase {
        // Access the serialized expression
        let serialized = serde_json::to_string(&self).unwrap();
        let value: Value = serde_json::from_str(&serialized).unwrap();
        let representation = json!({
            "entities": self.entities,
            "expression": value.get("expression").unwrap().to_string(),
            "request": format!("{}", &self.request),
        });
        FuzzTestCase {
            representation: representation.to_string(),
            ..Default::default()
        }
    }
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 3,
    max_width: 3,
    enable_additional_attributes: false,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
};

fn main() {
    check!()
        .with_arbitrary::<FuzzTargetInput>()
        .for_each(|input| {
            initialize_log();
            let def_impl = LeanDefinitionalEngine::new();
            debug!("expr: {}\n", input.expression);
            debug!("Entities: {}\n", input.entities);
            let obs_out = input.to_fuzz_test_case();
            run_eval_test(
                &def_impl,
                input.request.clone().into(),
                &input.expression,
                &input.entities,
                SETTINGS.enable_extensions,
            );
            if let Ok(_) = std::env::var("DRT_OBSERVABILITY") {
                let dirname = "fuzz/observations";
                let testname = std::env::var("FUZZ_TARGET").unwrap_or("eval-derived".to_string());
                dump_fuzz_test_case(dirname, &testname, &obs_out)
            }
        });
}
