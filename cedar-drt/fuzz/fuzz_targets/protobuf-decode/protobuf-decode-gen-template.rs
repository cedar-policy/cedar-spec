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

use cedar_drt_inner::proto_gen::ModelGenerator;
use cedar_drt_inner::{fuzz_target, props::template_to_cedar_parses};

use cedar_policy::Template;
use cedar_policy::proto::models;
use prost::Message;

use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Fuzz input: a directly-generated protobuf TemplateBody (no slots).
#[derive(Debug, Clone)]
struct ProtoTemplateInput {
    template: models::TemplateBody,
}

impl<'a> Arbitrary<'a> for ProtoTemplateInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let g = ModelGenerator::arbitrary(u)?;
        Ok(Self {
            template: g.arbitrary_model_template_body(u, false)?,
        })
    }
}

// Generate a proto TemplateBody → encode to bytes → decode → convert to domain →
// print to Cedar text → re-parse.
// Property: if decode+conversion succeeds, printing and re-parsing must also succeed.
fuzz_target!(|input: ProtoTemplateInput| {
    // Encode the generated proto model to bytes
    let buf = input.template.encode_to_vec();

    // Decode from bytes
    let decoded = models::TemplateBody::decode(&buf[..])
        .expect("Decoding an encoded models::Template failed.");

    // Convert proto model → domain type
    // We expect this to fail, but when this doesn't faill all subsequent steps should pass.
    let template = match Template::try_from(decoded) {
        Ok(t) => t,
        Err(_) => return,
    };
    // Once we have a template, it should parse again through a Cedar roundtrip: we test that
    // validation in the Cedar parser is not stronger than validation in protobuf.
    template_to_cedar_parses(template);
});
