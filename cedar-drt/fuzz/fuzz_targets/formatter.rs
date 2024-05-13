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

use cedar_drt::initialize_log;
use cedar_drt_inner::fuzz_target;
use cedar_policy_core::ast::{AnyId, EntityType, ExprKind, Literal, StaticPolicy, Template};
use cedar_policy_core::parser::{self, parse_policy};
use cedar_policy_formatter::{lexer, policies_str_to_pretty, Config};
use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema::Schema, settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use serde::Serialize;
use similar_asserts::SimpleDiff;
use smol_str::SmolStr;
use std::collections::HashMap;
use uuid::Uuid;

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

// Attach each token two uuids as leading comment and one uuid as trailing comment
fn attach_comment(p: &str, uuids: &mut Vec<String>) -> String {
    let mut tokens = lexer::get_token_stream(p).expect("tokens should exist");
    for t in tokens.iter_mut() {
        let mut ids: Vec<String> = [Uuid::new_v4(), Uuid::new_v4(), Uuid::new_v4()]
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
    let commented = attach_comment(&p.to_string(), &mut uuids);
    let formatted_policy_str =
        &policies_str_to_pretty(&commented, &config).expect("pretty-printing should not fail");
    // check if pretty-printing drops any comment
    let mut formatted_policy_tail: &str = formatted_policy_str.as_str();
    for u in &uuids {
        match formatted_policy_tail.split_once(u) {
            Some((_, after_uuid)) => formatted_policy_tail = after_uuid,
            None => {
                println!(
                    "{}",
                    SimpleDiff::from_str(
                        &commented,
                        formatted_policy_str,
                        "Commented Policy",
                        "Commented and formatted"
                    )
                );
                if formatted_policy_str.contains(u) {
                    panic!("It looks like we skipped over comment `{u}`. The formatter might have reordered the comment")
                } else {
                    panic!("Failed to find comment `{u}` anywhere. The formatter might have dropped the comment")
                }
            }
        }
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
        Ok(roundtripped) => {
            assert!(
                t.slots().collect::<Vec<_>>().is_empty(),
                "\nold template slots should be empty\n"
            );
            // just dump to standard hashmaps to check equality without order.
            // also ignore source locations, which are not preserved in this roundtrip
            let roundtripped_anno: HashMap<&AnyId, &SmolStr> = roundtripped
                .annotations()
                .map(|(k, v)| (k, &v.val))
                .collect();
            let original_anno: HashMap<&AnyId, &SmolStr> =
                t.annotations().map(|(k, v)| (k, &v.val)).collect();
            assert_eq!(
                original_anno, roundtripped_anno,
                "\nannotations should be the same, found:\noriginal: {original_anno:?}\nroundtripped: {roundtripped_anno:?}\n",
            );
            assert_eq!(
                roundtripped.effect(),
                t.effect(),
                "\nnew effect: {:?}\nold effect: {:?}\n",
                roundtripped.effect(),
                t.effect()
            );
            assert_eq!(
                roundtripped.principal_constraint(),
                t.principal_constraint(),
                "\nnew principal constraint: {:?}\nold principal constraint: {:?}\n",
                roundtripped.principal_constraint(),
                t.principal_constraint()
            );
            assert_eq!(
                roundtripped.action_constraint(),
                t.action_constraint(),
                "\nnew action constraint: {:?}\nold action constraint: {:?}\n",
                roundtripped.action_constraint(),
                t.action_constraint()
            );
            assert_eq!(
                roundtripped.resource_constraint(),
                t.resource_constraint(),
                "\nnew resource constraint: {:?}\nold resource constraint: {:?}\n",
                roundtripped.resource_constraint(),
                t.resource_constraint()
            );
            assert!(
                roundtripped
                    .non_scope_constraints()
                    .eq_shape(t.non_scope_constraints()),
                "\nnew policy condition: {}\nold policy condition: {}\n",
                roundtripped.non_scope_constraints(),
                t.non_scope_constraints(),
            );
        }
        Err(err) => panic!(
            "\nInvalid AST captured: {:?}\n pp form: {}\n parsing error: {:?}\n",
            p, p, err
        ),
    }
});
