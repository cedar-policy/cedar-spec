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
use cedar_policy_core::ast::{EntityType, ExprKind, Literal, StaticPolicy, Template};
use cedar_policy_core::parser::{self, parse_policy};
use cedar_policy_formatter::{lexer, policies_str_to_pretty, Config};
use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema::Schema, settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use uuid::Uuid;

// A thin wrapper for policy
#[derive(Debug, Clone)]
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

// Attach each token two uuids as leading comment and one uuid as trailing comment
fn attach_comment(p: &str, uuids: &mut Vec<String>) -> String {
    let mut tokens = lexer::get_token_stream(p);
    for t in tokens.iter_mut() {
        let mut ids: Vec<String> = vec![Uuid::new_v4(), Uuid::new_v4(), Uuid::new_v4()]
            .iter()
            .map(|u| u.to_string())
            .collect();
        let leading_comment = format!("\n//{}\n//{}\n", ids[0], ids[1]);
        let trailing_comment = format!("//{}\n", ids[2]);
        t.add_leading_comment(&leading_comment);
        t.add_trailing_comment(&trailing_comment);
        uuids.append(&mut ids);
    }
    tokens
        .iter()
        .map(|t| t.to_string())
        .collect::<Vec<_>>()
        .join("")
}

// round-tripping of a policy
// i.e., print a policy to string, format it, and parse it back
fn round_trip(p: &StaticPolicy) -> Result<StaticPolicy, parser::err::ParseErrors> {
    let config = Config {
        indent_width: 2,
        line_width: 80,
    };
    let mut uuids = Vec::new();
    let formatted_policy_str =
        &policies_str_to_pretty(&attach_comment(&p.to_string(), &mut uuids), &config)
            .expect("pretty-printing should not fail");
    // check if pretty-printing drops any comment
    for u in &uuids {
        assert!(formatted_policy_str.contains(u), "missing comment: {}\n", u);
    }
    parse_policy(None, formatted_policy_str)
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
    let (t, _) = Template::link_static_policy(p.clone());

    debug!("Starting policy: {:?}", p);
    // round-tripping over it should preserve syntactical equivalence.
    // Note that we are ignoring IDs, because Cedar does not
    // get ids from policy text
    match round_trip(&p) {
        Ok(np) => {
            assert!(
                t.slots().collect::<Vec<_>>().is_empty(),
                "\nold template slots should be empty\n"
            );
            // just dump to standard hashmaps to check equality without order
            let old_anno = np
                .annotations()
                .collect::<std::collections::HashMap<_, _>>();
            let new_anno = t.annotations().collect::<std::collections::HashMap<_, _>>();
            assert_eq!(
                old_anno, new_anno,
                "\nannotations should be the same, found:\nold: {:?}\nnew: {:?}\n",
                old_anno, new_anno,
            );
            assert_eq!(
                np.effect(),
                t.effect(),
                "\nnew effect: {:?}\nold effect: {:?}\n",
                np.effect(),
                t.effect()
            );
            assert_eq!(
                np.principal_constraint(),
                t.principal_constraint(),
                "\nnew principal constraint: {:?}\nold principal constraint: {:?}\n",
                np.principal_constraint(),
                t.principal_constraint()
            );
            assert_eq!(
                np.action_constraint(),
                t.action_constraint(),
                "\nnew action constraint: {:?}\nold action constraint: {:?}\n",
                np.action_constraint(),
                t.action_constraint()
            );
            assert_eq!(
                np.resource_constraint(),
                t.resource_constraint(),
                "\nnew resource constraint: {:?}\nold resource constraint: {:?}\n",
                np.resource_constraint(),
                t.resource_constraint()
            );
            assert!(
                np.non_head_constraints().eq_shape(t.non_head_constraints()),
                "\nnew policy condition: {}\nold policy condition: {}\n",
                np.non_head_constraints(),
                t.non_head_constraints(),
            );
        }
        Err(err) => panic!(
            "\nInvalid AST captured: {:?}\n pp form: {}\n, parsing error: {:?}\n",
            p, p, err
        ),
    }
});
