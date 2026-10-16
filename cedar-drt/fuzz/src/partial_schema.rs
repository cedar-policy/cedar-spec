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

//! Generation and comparison for partial-schema validation DRT.
//!
//! A complete generated schema is externalized before Rust and Lean validate
//! the same entities and requests against it.

use cedar_lean_ffi::{CedarLeanFfi, ValidationResponse};
use cedar_policy::{Entities, Entity, Request, Schema, SchemaFragment};
use cedar_policy_core::validator::RawName;
use cedar_policy_core::validator::json_schema::{self, EntityTypeKind, StandardEntityType};
use cedar_policy_generators::{
    abac::ABACRequest, hierarchy::HierarchyGenerator, schema, schema_gen::SchemaGen,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

use crate::schemas::add_actions_to_entities;

const SETTINGS: ABACSettings = ABACSettings {
    enable_additional_attributes: true,
    ..ABACSettings::undirected()
};
const NUM_REQUESTS: usize = 8;

#[derive(Debug, Clone)]
pub struct PartialSchemaInput {
    pub complete: Schema,
    pub partial: Schema,
    pub entities: Entities,
    pub requests: Vec<Request>,
}

impl<'a> Arbitrary<'a> for PartialSchemaInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let generated = schema::Schema::arbitrary(SETTINGS, u)?;
        let hierarchy = generated.arbitrary_hierarchy(u)?;
        let abac_requests = (0..NUM_REQUESTS)
            .map(|_| generated.arbitrary_request(&hierarchy, u))
            .collect::<Result<Vec<_>, _>>()?;
        let complete =
            Schema::try_from(generated).map_err(|_| arbitrary::Error::IncorrectFormat)?;
        let entities = add_actions_to_entities(
            &complete,
            Entities::try_from(hierarchy).map_err(|_| arbitrary::Error::NotEnoughData)?,
        )?;
        let requests = abac_requests
            .into_iter()
            .map(|r: ABACRequest| cedar_policy_core::ast::Request::from(r).into())
            .collect();
        let partial = externalize(&complete, u)?.ok_or(arbitrary::Error::IncorrectFormat)?;
        let entities = filter_externalized_instances(&entities, &partial);
        Ok(Self {
            complete,
            partial,
            entities,
            requests,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        let mut hints = vec![
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
        ];
        hints.extend(std::iter::repeat_n(
            schema::Schema::arbitrary_request_size_hint(depth),
            NUM_REQUESTS,
        ));
        Ok(arbitrary::size_hint::and_all(&hints))
    }
}

/// Rewrite `et` into an `external` declaration, which keeps only its parents.
pub(crate) fn declare_entity_type_external<N: Clone>(et: &mut json_schema::EntityType<N>) {
    let member_of_types = match &et.kind {
        EntityTypeKind::Standard(std) => std.member_of_types.clone(),
        // An enum has no parents. Callers exclude enums, since RFC 116 does not
        // allow linking a declaration to one; this arm keeps the rewrite total.
        EntityTypeKind::Enum { .. } => vec![],
    };
    et.kind = EntityTypeKind::Standard(StandardEntityType {
        member_of_types,
        shape: json_schema::AttributesOrContext::default(),
        tags: None,
    });
    et.external = true;
}

/// Rewrite `at` into an `external` declaration, which keeps only its parents.
pub(crate) fn declare_action_external<N>(at: &mut json_schema::ActionType<N>) {
    at.applies_to = None;
    at.attributes = None;
    at.external = true;
}

/// `None` if `fragment` does not build.
pub(crate) fn schema_from_fragment(fragment: json_schema::Fragment<RawName>) -> Option<Schema> {
    Schema::from_schema_fragments([SchemaFragment::try_from(fragment).ok()?]).ok()
}

/// Externalize each declaration independently with probability 1/2. Enums are
/// never selected, since RFC 116 does not allow linking a declaration to one.
pub fn declare_some_external<N: Clone>(
    fragment: &mut json_schema::Fragment<N>,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<()> {
    for nsdef in fragment.0.values_mut() {
        for et in nsdef.entity_types.values_mut() {
            if !et.external && matches!(et.kind, EntityTypeKind::Standard(_)) && u.ratio(1, 2)? {
                declare_entity_type_external(et);
            }
        }
        for at in nsdef.actions.values_mut() {
            if !at.external && u.ratio(1, 2)? {
                declare_action_external(at);
            }
        }
    }
    Ok(())
}

/// `None` if the externalized schema does not build.
fn externalize(schema: &Schema, u: &mut Unstructured<'_>) -> arbitrary::Result<Option<Schema>> {
    let mut fragment: json_schema::Fragment<RawName> = schema
        .as_ref()
        .to_json_schema()
        .expect("a complete, generated schema should convert to `json_schema`");
    declare_some_external(&mut fragment, u)?;
    Ok(schema_from_fragment(fragment))
}

/// Drop every instance of a declaration `partial` only declares `external`.
/// Entities of such a type cannot be validated at all, so a hierarchy holding
/// one is always rejected; dropping them gives an input both sides accept.
fn filter_externalized_instances(entities: &Entities, partial: &Schema) -> Entities {
    let kept: Vec<Entity> = entities
        .iter()
        .filter(|e| {
            let uid = e.uid();
            !partial
                .external_entity_types()
                .any(|t| t == uid.type_name())
                && !partial.external_actions().any(|a| a == &uid)
        })
        .cloned()
        .collect();
    Entities::from_entities(kept, None)
        .expect("dropping entities from an existing, duplicate-free `Entities` cannot fail")
}

fn lean_accepted(response: &ValidationResponse) -> bool {
    matches!(response, ValidationResponse::Ok(()))
}

/// Run the differential comparison for one generated input. Panics, with the
/// schemas and the offending input, on any disagreement or FFI failure.
pub fn check_agreement(ffi: &CedarLeanFfi, input: &PartialSchemaInput) {
    let partial = &input.partial;
    let context = || {
        format!(
            "complete schema: {:?}\npartial schema: {:?}",
            input.complete, partial
        )
    };

    let entities = &input.entities;
    let rust_accepted = Entities::from_entities(entities.iter().cloned(), Some(partial)).is_ok();
    let response = ffi
        .validate_entities_partial_schema(partial, entities)
        .unwrap_or_else(|e| {
            panic!(
                "`validate_entities_partial_schema` failed: {e}\n{}\nentities: {entities:#?}",
                context()
            )
        });
    assert_eq!(
        rust_accepted,
        lean_accepted(&response),
        "entity validation disagreement\nRust accepted: {rust_accepted}\n\
         Lean response: {response:?}\n{}\nentities: {entities:#?}",
        context()
    );

    for request in &input.requests {
        let rust_accepted = Request::new(
            request.principal().expect("concrete principal").clone(),
            request.action().expect("concrete action").clone(),
            request.resource().expect("concrete resource").clone(),
            request.context().expect("concrete context").clone(),
            Some(partial),
        )
        .is_ok();
        let response = ffi
            .validate_request_partial_schema(partial, request)
            .unwrap_or_else(|e| {
                panic!(
                    "`validate_request_partial_schema` failed: {e}\n{}\nrequest: {request}",
                    context()
                )
            });
        assert_eq!(
            rust_accepted,
            lean_accepted(&response),
            "request validation disagreement\n\
             Rust accepted: {rust_accepted}\nLean response: {response:?}\n{}\n\
             request: {request}",
            context()
        );
    }
}
