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
use cedar_policy_core::ast;
use cedar_policy_core::ast::{EntityType, ExprKind, Literal, StaticPolicy, Template};
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
    match_types: false,
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

// Round-tripping using the display trait: print a policy to string and parse it back.
fn round_trip(p: &StaticPolicy) -> Result<StaticPolicy, parser::err::ParseErrors> {
    parse_policy(None, &p.to_string())
}

// Round-tripping using the JSON (EST) format: print a policy to a JSON string
// and parse it back. Panics if any step fails.
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
    let (t, _) = Template::link_static_policy(p1.clone());
    assert!(
        t.slots().collect::<Vec<_>>().is_empty(),
        "\nold template slots should be empty\n"
    );
    // just dump to standard hashmaps to check equality without order
    let old_anno = p2
        .annotations()
        .collect::<std::collections::HashMap<_, _>>();
    let new_anno = t.annotations().collect::<std::collections::HashMap<_, _>>();
    assert_eq!(
        old_anno, new_anno,
        "\nannotations should be the same, found:\nold: {:?}\nnew: {:?}\n",
        old_anno, new_anno,
    );
    assert_eq!(
        p2.effect(),
        t.effect(),
        "\nnew effect: {:?}\nold effect: {:?}\n",
        p2.effect(),
        t.effect()
    );
    assert_eq!(
        p2.principal_constraint(),
        t.principal_constraint(),
        "\nnew principal constraint: {:?}\nold principal constraint: {:?}\n",
        p2.principal_constraint(),
        t.principal_constraint()
    );
    assert_eq!(
        p2.action_constraint(),
        t.action_constraint(),
        "\nnew action constraint: {:?}\nold action constraint: {:?}\n",
        p2.action_constraint(),
        t.action_constraint()
    );
    assert_eq!(
        p2.resource_constraint(),
        t.resource_constraint(),
        "\nnew resource constraint: {:?}\nold resource constraint: {:?}\n",
        p2.resource_constraint(),
        t.resource_constraint()
    );
    assert!(
        p2.non_head_constraints().eq_shape(t.non_head_constraints()),
        "\nnew policy condition: {:?}\nold policy condition: {:?}\n",
        p2.non_head_constraints(),
        t.non_head_constraints()
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

    debug!("Starting policy: {:?}", p);
    match round_trip(&p) {
        Ok(np) => {
            check_policy_equivalence(&p, &np);
        }
        Err(err) => panic!(
            "\nInvalid AST captured: {:?}\n pp form: {}\n, parsing error: {:?}\n",
            p, p, err
        ),
    }
    let np = round_trip_json(p.clone());
    check_policy_equivalence(&p, &np);
});
