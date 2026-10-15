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

//! Generation and comparison for partial-schema linking DRT.
//!
//! Inputs include complementary partitions and independently generated partial
//! schemas.

use cedar_lean_ffi::{CedarLeanFfi, ValidationResponse};
use cedar_policy::Schema;
use cedar_policy_core::validator::RawName;
use cedar_policy_core::validator::json_schema::{self, EntityTypeKind};
use cedar_policy_generators::{schema, settings::ABACSettings};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

use crate::partial_schema::{
    declare_action_external, declare_entity_type_external, declare_some_external,
    schema_from_fragment,
};

const SETTINGS: ABACSettings = ABACSettings::undirected();

#[derive(Debug, Clone)]
pub struct SchemaLinkInput {
    pub first: Schema,
    pub second: Schema,
    /// Known result for complementary partitions. `None` means the outcome is
    /// not predetermined, not that linking should fail.
    pub expected: Option<Schema>,
}

impl<'a> Arbitrary<'a> for SchemaLinkInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let complete = arbitrary_schema(u)?;
        if u.arbitrary()? {
            if has_action_entity_type(&complete) {
                return Err(arbitrary::Error::IncorrectFormat);
            }
            let (first, second) =
                partition(&complete, u)?.ok_or(arbitrary::Error::IncorrectFormat)?;
            Ok(Self {
                first,
                second,
                expected: Some(complete),
            })
        } else {
            Ok(Self {
                first: random_partial(&complete, u)?,
                second: random_partial(&arbitrary_schema(u)?, u)?,
                expected: None,
            })
        }
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        schema::Schema::arbitrary_size_hint(depth)
    }
}

fn arbitrary_schema(u: &mut Unstructured<'_>) -> arbitrary::Result<Schema> {
    Schema::try_from(schema::Schema::arbitrary(SETTINGS, u)?)
        .map_err(|_| arbitrary::Error::IncorrectFormat)
}

fn schema_fragment(schema: &Schema) -> json_schema::Fragment<RawName> {
    schema
        .as_ref()
        .to_json_schema()
        .expect("a generated schema should convert to `json_schema`")
}

fn random_partial(schema: &Schema, u: &mut Unstructured<'_>) -> arbitrary::Result<Schema> {
    let mut fragment = schema_fragment(schema);
    declare_some_external(&mut fragment, u)?;
    schema_from_fragment(fragment).ok_or(arbitrary::Error::IncorrectFormat)
}

fn has_action_entity_type(schema: &Schema) -> bool {
    let action_types: Vec<_> = schema.actions().map(|a| a.type_name().clone()).collect();
    schema.entity_types().any(|ety| action_types.contains(ety))
}

/// Split `schema` into two partial schemas, as the module docs describe.
/// `None` if either half does not build.
fn partition(
    schema: &Schema,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<Option<(Schema, Schema)>> {
    let full: json_schema::Fragment<RawName> = schema
        .as_ref()
        .to_json_schema()
        .expect("a complete, generated schema should convert to `json_schema`");
    let mut first = full.clone();
    let mut second = full.clone();

    for (ns, nsdef) in full.0.iter() {
        for (name, entity_type) in &nsdef.entity_types {
            let partial = if u.arbitrary()? {
                &mut second
            } else {
                &mut first
            };
            let entity_types = &mut partial
                .0
                .get_mut(ns)
                .expect("both halves were cloned from the same fragment")
                .entity_types;
            if matches!(entity_type.kind, EntityTypeKind::Enum { .. }) {
                // External declarations cannot resolve to enums, so define the
                // enum in one half and omit it from the other.
                entity_types.remove(name);
            } else {
                declare_entity_type_external(
                    entity_types
                        .get_mut(name)
                        .expect("both halves contain the entity type"),
                );
            }
        }
        for id in nsdef.actions.keys() {
            let declarer = if u.arbitrary()? {
                &mut second
            } else {
                &mut first
            };
            declare_action_external(
                declarer
                    .0
                    .get_mut(ns)
                    .and_then(|nsdef| nsdef.actions.get_mut(id))
                    .expect("both halves were cloned from the same fragment"),
            );
        }
    }

    Ok(
        match (schema_from_fragment(first), schema_from_fragment(second)) {
            (Some(first), Some(second)) => Some((first, second)),
            _ => None,
        },
    )
}

fn fail(message: &str, input: &SchemaLinkInput, response: Option<&ValidationResponse>) -> ! {
    panic!(
        "{message}\nLean response: {response:?}\nexpected link: {:?}\n\
         first schema: {:?}\nsecond schema: {:?}",
        input.expected, input.first, input.second
    )
}

/// Compare Rust and Lean linking outcomes and, on success, linked schemas.
pub fn check_agreement(ffi: &CedarLeanFfi, input: &SchemaLinkInput) {
    let linked = Schema::schema_link([input.first.clone(), input.second.clone()]);
    let response = ffi
        .link_partial_schemas(&input.first, &input.second, linked.as_ref().ok())
        .unwrap_or_else(|e| fail(&format!("`link_partial_schemas` failed: {e}"), input, None));
    if !matches!(response, ValidationResponse::Ok(())) {
        fail(
            "the Rust linker and the model disagree",
            input,
            Some(&response),
        );
    }
}

/// For complementary partitions, independently check the known linked schema.
pub fn check_expected_link(ffi: &CedarLeanFfi, input: &SchemaLinkInput) {
    let Some(expected) = &input.expected else {
        return;
    };
    let response = ffi
        .link_partial_schemas(&input.first, &input.second, Some(expected))
        .unwrap_or_else(|e| fail(&format!("`link_partial_schemas` failed: {e}"), input, None));
    if !matches!(response, ValidationResponse::Ok(())) {
        fail(
            "linking did not produce the expected schema",
            input,
            Some(&response),
        );
    }
}
