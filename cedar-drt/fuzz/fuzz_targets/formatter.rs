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

use cedar_drt::check_policy_equivalence;
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::fuzz_target;

use cedar_policy_core::ast::{StaticPolicy, Template};
use cedar_policy_core::parser::{self, parse_policy};
use cedar_policy_formatter::token::{Comment, Token, WrappedToken};
use cedar_policy_formatter::{policies_str_to_pretty, Config};
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema::Schema, settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use logos::Logos;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use similar_asserts::SimpleDiff;
use std::sync::Arc;
use uuid::Builder;

// A thin wrapper for policy
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    // the generated policy
    policy: ABACPolicy,
    // seed to generate random UUIDs
    seed: u64,
}

// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    enable_additional_attributes: true,
    enable_arbitrary_func_call: false,
    ..ABACSettings::undirected()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        let seed = u.arbitrary()?;
        Ok(Self { policy, seed })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            <u64 as Arbitrary>::size_hint(depth),
        ]))
    }
}

// Attach each token two uuids as leading comment and one uuid as trailing comment
fn attach_comment(p: &str, uuids: &mut Vec<String>, seed: u64) -> String {
    let mut rng = SmallRng::seed_from_u64(seed);
    let mut build_uuid = || Builder::from_random_bytes(rng.random()).into_uuid();

    Token::lexer(p)
        .spanned()
        .map(|t| {
            let mut ids: Vec<String> = [build_uuid(), build_uuid(), build_uuid()]
                .iter()
                .map(|u| u.to_string())
                .collect();
            let leading_comment = format!("\n//{}\n//{}\n", ids[0], ids[1]);
            let trailing_comment = format!("//{}\n", ids[2]);
            uuids.append(&mut ids);
            WrappedToken::new(
                t.0.unwrap(),
                t.1,
                Comment::new(&leading_comment, &trailing_comment),
            )
            .to_string()
        })
        .collect::<Vec<_>>()
        .join("")
}

// round-tripping of a policy
// i.e., print a policy to string, format it, and parse it back
fn round_trip(p: &StaticPolicy, seed: u64) -> Result<StaticPolicy, Box<parser::err::ParseErrors>> {
    let config = Config {
        indent_width: 2,
        line_width: 80,
    };
    let mut uuids = Vec::new();
    let commented = attach_comment(&p.to_string(), &mut uuids, seed);
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
    Ok(parse_policy(None, formatted_policy_str)?)
}

fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let seed = input.seed;
    let p: StaticPolicy = input.policy.into();
    let (t, _) = Template::link_static_policy(p.clone());

    debug!("Starting policy: {:?}", p);
    // round-tripping over it should preserve syntactical equivalence.
    // Note that we are ignoring IDs, because Cedar does not
    // get ids from policy text
    match round_trip(&p, seed) {
        Ok(roundtripped) => {
            assert!(
                t.slots().collect::<Vec<_>>().is_empty(),
                "\nold template slots should be empty\n"
            );
            check_policy_equivalence(
                &Into::<Arc<Template>>::into(p),
                &Into::<Arc<Template>>::into(roundtripped),
            );
        }
        Err(err) => panic!(
            "\nInvalid AST captured: {:?}\n pp form: {}\n parsing error: {:?}\n",
            p, p, err
        ),
    }
});
