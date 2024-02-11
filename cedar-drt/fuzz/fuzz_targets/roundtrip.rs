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

use cedar_drt::initialize_log;
use cedar_drt_inner::fuzz_target;
use cedar_policy_core::ast::{self, EntityType, ExprKind, Literal, StaticPolicy, Template};
use cedar_policy_core::est;
use cedar_policy_core::parser::{self, parse_policy};
use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema::Schema, settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use serde::Serialize;

// A thin wrapper for policy
#[derive(Debug, Clone, Serialize)]
struct FuzzTargetInput {
    // the generated policy
    policy: ABACPolicy,
}

// settings for this fuzz target
// copy-pasted from abac.rs
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: true,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: false,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        Ok(Self { policy })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
        ])
    }
}

fn contains_unspecified_entities(p: &StaticPolicy) -> bool {
    p.condition().subexpressions().any(|e| matches!(e.expr_kind(), ExprKind::Lit(Literal::EntityUID(euid)) if matches!(*euid.entity_type(), EntityType::Unspecified)))
}

// Print a policy to a string and parse it back using the standard AST parser.
// Panics if parsing fails.
fn round_trip_ast(p: &StaticPolicy) -> StaticPolicy {
    parse_policy(None, &p.to_string()).unwrap_or_else(|err| {
        panic!(
            "Failed to round-trip AST: {:?}\nPretty printed form: {}\nParse error: {:?}\n",
            p, p, err
        )
    })
}

// Print a policy to a string, parse it back using the EST parser, and convert to JSON.
// Panics if any step fails. The resulting policy may be different from the input
// (since the roundtrip is lossy), so this function only checks that the round-trip
// succeeds without error.
fn round_trip_est(p: &StaticPolicy) {
    let est = parser::parse_policy_or_template_to_est(&p.to_string()).unwrap_or_else(|err| {
        panic!(
            "Failed to round-trip EST: {:?}\nPretty printed form: {}\nParse error: {:?}\n",
            p, p, err
        )
    });
    serde_json::to_value(est).unwrap_or_else(|err| {
        panic!(
            "Failed to convert EST to JSON: {:?}\nParse error: {:?}\n",
            p, err
        )
    });
}

// Print a policy to a JSON string and parse it back. Panics if any step fails.
fn round_trip_json(p: StaticPolicy) -> StaticPolicy {
    // convert to json
    let est = est::Policy::from(ast::Policy::from(p));
    let json = serde_json::to_value(est).expect("failed to convert EST to JSON");
    // read back
    let est: est::Policy = serde_json::from_value(json).expect("failed to parse EST from JSON");
    let template = est
        .try_into_ast_template(None)
        .expect("failed to convert EST to AST");
    template
        .try_into()
        .expect("failed to convert `Template` to `StaticPolicy`")
}

// Check that round-tripping preserves syntactic equivalence.
// Panic if the two policies are not the same, ignoring ids.
fn check_policy_equivalence(p1: &StaticPolicy, p2: &StaticPolicy) {
    let (t1, _) = Template::link_static_policy(p1.clone());
    assert!(
        t1.slots().collect::<Vec<_>>().is_empty(),
        "\nold template slots should be empty\n"
    );
    // just dump to standard hashmaps to check equality without order
    let old_anno = p2
        .annotations()
        .collect::<std::collections::HashMap<_, _>>();
    let new_anno = t1
        .annotations()
        .collect::<std::collections::HashMap<_, _>>();
    assert_eq!(
        old_anno, new_anno,
        "\nannotations should be the same, found:\nold: {:?}\nnew: {:?}\n",
        old_anno, new_anno,
    );
    assert_eq!(
        p2.effect(),
        t1.effect(),
        "\nnew effect: {:?}\nold effect: {:?}\n",
        p2.effect(),
        t1.effect()
    );
    assert_eq!(
        p2.principal_constraint(),
        t1.principal_constraint(),
        "\nnew principal constraint: {:?}\nold principal constraint: {:?}\n",
        p2.principal_constraint(),
        t1.principal_constraint()
    );
    assert_eq!(
        p2.action_constraint(),
        t1.action_constraint(),
        "\nnew action constraint: {:?}\nold action constraint: {:?}\n",
        p2.action_constraint(),
        t1.action_constraint()
    );
    assert_eq!(
        p2.resource_constraint(),
        t1.resource_constraint(),
        "\nnew resource constraint: {:?}\nold resource constraint: {:?}\n",
        p2.resource_constraint(),
        t1.resource_constraint()
    );
    assert!(
        p2.non_head_constraints()
            .eq_shape(t1.non_head_constraints()),
        "\nnew policy condition: {:?}\nold policy condition: {:?}\n",
        p2.non_head_constraints(),
        t1.non_head_constraints()
    );
}

fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let p: StaticPolicy = input.policy.into();
    // Version 1.2 introduces an unspecified entity type.
    // An entity of such type prints to an invalid string,
    // which further causes round-tripping to fail.
    // The fix is to add a filter to the generated policies,
    // so that we don't fuzz any policies with unspecified entities.
    if contains_unspecified_entities(&p) {
        return;
    }

    debug!("Running on policy: {:?}", p);

    // round-trip AST & check the returned policy
    let np = round_trip_ast(&p);
    check_policy_equivalence(&p, &np);

    // round-trip EST & check for failures
    round_trip_est(&p);

    // round-trip EST (via JSON) & check the returned policy
    let np = round_trip_json(p.clone());
    check_policy_equivalence(&p, &np);
});
