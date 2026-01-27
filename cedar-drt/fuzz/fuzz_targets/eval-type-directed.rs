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
use cedar_drt::{
    logger::initialize_log,
    tests::{drop_some_entities, run_eval_test},
};
use cedar_drt_inner::fuzz_target;

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::Entities;
use cedar_policy_core::ast::Expr;
use cedar_policy_generators::hierarchy::HierarchyGenerator;
use cedar_policy_generators::schema::{Schema, arbitrary_schematype_with_bounded_depth};
use cedar_policy_generators::settings::ABACSettings;
use cedar_policy_generators::{abac::ABACRequest, schema::schematype_to_type};
use cedar_policy_generators::{err::Error, schema_gen::SchemaGen};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// generated entity slice
    pub entities: Entities,
    /// generated expression
    pub expression: Expr,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    pub request: ABACRequest,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    max_depth: 3,
    max_width: 3,
    ..ABACSettings::type_directed()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let toplevel_type = schematype_to_type(
            schema.schemafile(),
            &arbitrary_schematype_with_bounded_depth(
                &SETTINGS,
                schema.entity_types(),
                SETTINGS.max_depth,
                u,
            )?,
            schema.namespace(),
        );
        let expr_gen = schema.exprgenerator(Some(&hierarchy));
        let expression = expr_gen.generate_expr_for_type(&toplevel_type, SETTINGS.max_depth, u)?;

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

// Type-directed fuzzing of expression evaluation.
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let def_impl = CedarLeanFfi::new();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("expr: {}\n", input.expression);
    debug!("Entities: {}\n", input.entities.as_ref());
    run_eval_test(
        &def_impl,
        &input.request.into(),
        &input.expression.into(),
        &input.entities,
    )
});
