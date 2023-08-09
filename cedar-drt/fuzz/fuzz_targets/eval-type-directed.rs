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
use cedar_drt::*;
use cedar_drt_inner::*;
use cedar_policy_core::ast::{self, Expr, StaticPolicy};
use cedar_policy_core::entities::{Entities, TCComputation};
use cedar_policy_generators::abac::ABACRequest;
use cedar_policy_generators::err::Error;
use cedar_policy_generators::expr::ExprGenerator;
use cedar_policy_generators::hierarchy::HierarchyGenerator;
use cedar_policy_generators::schema::{arbitrary_schematype_with_bounded_depth, Schema};
use cedar_policy_generators::settings::ABACSettings;
use cedar_policy_validator::SchemaType;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, info};
use std::convert::TryFrom;
use std::fs::OpenOptions;
use std::io::prelude::*;
use std::path::{Path, PathBuf};

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// generated entity slice
    pub entities: Entities,
    /// top level type of the policy
    pub toplevel_type: SchemaType,
    /// generated policy
    pub expression: Expr,
    /// the requests to try for this hirarchy and policy. We try 8 requests per
    /// policy/hierarchy
    pub requests: [ABACRequest; 1],
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
            // schema.arbitrary_request(&hierarchy, u)?,
            // schema.arbitrary_request(&hierarchy, u)?,
            // schema.arbitrary_request(&hierarchy, u)?,
            // schema.arbitrary_request(&hierarchy, u)?,
            // schema.arbitrary_request(&hierarchy, u)?,
            // schema.arbitrary_request(&hierarchy, u)?,
            // schema.arbitrary_request(&hierarchy, u)?,
        ];
        let all_entities = Entities::try_from(hierarchy).map_err(|_| Error::NotEnoughData)?;
        let entities = drop_some_entities(all_entities, u)?;
        Ok(Self {
            schema,
            entities,
            toplevel_type: toplevel_type.into(),
            expression,
            requests,
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

fn drop_some_entities(entities: Entities, u: &mut Unstructured<'_>) -> arbitrary::Result<Entities> {
    let should_drop: bool = u.arbitrary()?;
    if should_drop {
        let mut set: Vec<_> = vec![];
        for entity in entities.iter() {
            match u.int_in_range(0..=9)? {
                0 => (),
                _ => {
                    set.push(entity.clone());
                }
            }
        }
        Ok(
            Entities::from_entities(set.into_iter(), TCComputation::AssumeAlreadyComputed)
                .expect("Should be valid"),
        )
    } else {
        Ok(entities)
    }
}

fn get_next_name() -> String {
    let mut f = std::fs::File::open("/tmp/next_pol").unwrap();
    let mut s = String::new();
    f.read_to_string(&mut s).unwrap();
    let i: usize = s.trim().parse().unwrap();
    drop(f);
    let mut f = std::fs::OpenOptions::new()
        .write(true)
        .truncate(true)
        .open("/tmp/next_pol")
        .unwrap();
    write!(f, "{}", i + 1).unwrap();
    s
}

fn log_pol(p: &StaticPolicy) {
    let name = get_next_name();
    let mut path = PathBuf::new();
    path.push("/tmp");
    path.push("pols");
    path.push(name);
    let mut f = std::fs::File::create(path).unwrap();
    write!(f, "{p}").unwrap();
}

// The main fuzz target. This is for type-directed fuzzing of ABAC
// hierarchy/policy/requests
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let diff_tester = DifferentialTester::new();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("expr: {}\n", input.expression);
    debug!("Entities: {}\n", input.entities);
    let mut f = OpenOptions::new()
        .create(true)
        .write(true)
        .append(true)
        .open("./eval-policies.log")
        .unwrap();
    writeln!(f, "{}", input.expression).unwrap();
    drop(f);
    for q in input.requests.into_iter().map(Into::into) {
        assert!(diff_tester.run_eval_test(&q, &input.expression, &input.entities))
    }
});
