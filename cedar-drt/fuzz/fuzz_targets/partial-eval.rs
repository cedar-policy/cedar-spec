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
use cedar_drt::utils::expr_to_est;
use cedar_drt::*;
use cedar_drt_inner::*;
use cedar_policy_core::ast::Expr;
use cedar_policy_core::entities::Entities;
use cedar_policy_generators::schema::arbitrary_schematype_with_bounded_depth;
use cedar_policy_generators::{
    abac::ABACRequest, err::Error, hierarchy::HierarchyGenerator, schema::Schema,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use log::info;
use serde::Serialize;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, expression, and 8 associated requests
#[derive(Debug, Clone, Serialize)]
struct FuzzTargetInput {
    /// generated schema
    #[serde(skip)]
    pub schema: Schema,
    /// generated entity slice
    #[serde(skip)]
    pub entities: Entities,
    /// generated expression
    #[serde(serialize_with = "expr_to_est")]
    pub expression: Expr,
    /// the requests to try for this hierarchy and expression. We try 8 requests per
    /// policy/hierarchy
    #[serde(skip)]
    pub requests: [ABACRequest; 8],
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
    enable_unknowns: true,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
    // It's Ok to enable this flag because the diff tester ignores unknown extension function errors thrown by Lean
    enable_datetime_extension: true,
};

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
        let requests = [
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
        ];
        let all_entities = Entities::try_from(hierarchy).map_err(|_| Error::NotEnoughData)?;
        let entities = drop_some_entities(all_entities, u)?;
        Ok(Self {
            schema,
            entities,
            expression,
            requests,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
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
        ]))
    }
}
// The main fuzz target. This is for type-directed fuzzing of ABAC
// hierarchy/expression/requests
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let def_impl = LeanDefinitionalEngine::new();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("Expr: {:?}\n", input.expression);

    let request = input.requests.first().unwrap().clone().into();
    debug!("{request}");
    let ((), total_dur) =
        time_function(|| run_pe_test(&def_impl, request, &input.expression, &input.entities, true));

    info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
});
