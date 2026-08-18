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

use cedar_drt_inner::fuzz_target;
use cedar_drt_inner::props::expression_protobuf_decodes;

use cedar_policy::Expression;
use cedar_policy::proto::traits::{EncodeError, Protobuf};

use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_generators::{hierarchy::HierarchyGenerator, schema, settings::ABACSettings};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

#[derive(Debug, Clone)]
struct FuzzTargetInput {
    expression: Expression,
}

const SETTINGS: ABACSettings = ABACSettings {
    enable_arbitrary_func_call: false,
    ..ABACSettings::undirected()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: schema::Schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let mut expr_gen = schema.exprgenerator(Some(&hierarchy));
        let expr = expr_gen.generate_expr(SETTINGS.max_depth, u)?;
        Ok(Self {
            expression: Expression::from(expr),
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
        ]))
    }
}

// Generate an Expression using the ABAC generators, then encode to protobuf.
// Property: encoding a well-formed Expression must not panic, and decoding
// the result must succeed and produce an Expression that prints to Cedar and re-parses.
//
// This only tests parsing the encoded-decoded expression because Expression isn't PartialEq.
// The template and policyset targets already to test equality of policies, which tests equality
// between their conditions. If we really wanted to test equality here, we'd need equality for
// standalone expressions.
fuzz_target!(|input: FuzzTargetInput| {
    let buf = match input.expression.encode() {
        Ok(buf) => buf,
        Err(EncodeError::MaxDepthExceeded) => return,
        Err(e) => panic!("only error expected encoding Expression is MaxDepthExceeded, got {e}"),
    };
    expression_protobuf_decodes(&buf[..]);
});
