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

//! This module contains properties that API-level entities should satisfy.

use crate::roundtrip_entities::pretty_assert_entities_deep_eq;
use cedar_policy::{
    Entities, Entity, Expression, Policy, PolicySet, Request, RestrictedExpression, Schema,
    Template,
};
use cedar_policy_core::validator::ValidatorSchema;

/// An [`Entity`] should roundrtrip through serialization with json and then deserialization.
/// The [`Entity`] gets converted to a singleton [`Entities`].
pub fn entity_to_json_roundtrips(original: Entity) {
    // Wrap in Entities for JSON serialization
    let entities = Entities::from_entities([original], None)
        .expect("Failed to create Entities from single entity");
    entities_to_json_roundtrips(entities);
}

/// An [`Entities`] should roundtrip through serialization with json and then deserialization.
pub fn entities_to_json_roundtrips(original: Entities) {
    // Serialize to JSON
    let json = original.to_json_value().unwrap_or_else(|e| {
        panic!(
            "Entities could not be serialized to JSON.\n\
             Original: {:?}\nError: {e}",
            e
        )
    });

    // Re-parse from JSON
    let roundtripped = Entities::from_json_value(json.clone(), None).unwrap_or_else(|e| {
        panic!(
            "JSON from Entities failed to re-parse.\n\
             Original: {:?}\nJSON: {json}\nParse error: {e}",
            e
        )
    });

    pretty_assert_entities_deep_eq(&original, &roundtripped);
}

pub fn expression_to_cedar_parses(original: Expression) {
    // Print to cedar text, wrapped in a policy body
    let cedar_text = original.to_string();

    // Re-parse as a policy
    let _: Expression = cedar_text.parse().unwrap_or_else(|e| {
        panic!(
            "This Expression cannot be printed and parsed:\n{:?}\nParse error: {e}",
            original
        )
    });
}

/// A [`Template`] should print to Cedar and parse again. This function panic for inputs where
/// it does not.
pub fn template_to_cedar_parses(original: Template) {
    // Print to Cedar text
    let cedar_text = original.to_cedar();

    // Re-parse (templates parse as part of a policy set)
    let _: cedar_policy::PolicySet = cedar_text.parse().unwrap_or_else(|e| {
        panic!(
            "This cedar_policy::Template cannot be printed and parsed:\n{:?}\nParse error: {e}",
            original
        )
    });
}

/// A [`PolicySet`] should print to Cedar and parse again. This function panics for inputs where
/// it does not.
/// This also returns the [`PolicySet`] reconstructed by printing and parsing.
pub fn policyset_to_cedar_parses(original: PolicySet) -> PolicySet {
    let mut reconstructed = PolicySet::new();

    // Templates: print each to text, parse back with original ID
    for template in original.templates() {
        let id = template.id().clone();
        let text = template.to_string();
        let parsed = Template::parse(Some(id.clone()), &text).unwrap_or_else(|e| {
            panic!("Failed to parse template from text:\n{text}\nError: {e:?}")
        });
        reconstructed
            .add_template(parsed)
            .unwrap_or_else(|e| panic!("Failed to add template {id}: {e:?}"));
    }

    // Static policies: print each to text, parse back with original ID
    // Linked policies: re-link from template
    for policy in original.policies() {
        if let (Some(template_id), Some(links)) = (policy.template_id(), policy.template_links()) {
            reconstructed
                .link(template_id.clone(), policy.id().clone(), links)
                .unwrap_or_else(|e| panic!("Failed to link template {template_id}: {e:?}"));
        } else {
            let id = policy.id().clone();
            let text = policy.to_string();
            let parsed = Policy::parse(Some(id.clone()), &text).unwrap_or_else(|e| {
                panic!("Failed to parse policy from text:\n{text}\nError: {e:?}")
            });
            reconstructed
                .add(parsed)
                .unwrap_or_else(|e| panic!("Failed to add policy {id}: {e:?}"));
        }
    }
    reconstructed
}

/// A [`Request`]'s context values should each print to Cedar and re-parse. This tests that
/// protobuf decoding validation is not weaker than Cedar text parsing for context expressions.
pub fn request_context_to_cedar_parses(request: Request) {
    if let Some(context) = request.context() {
        for (key, value) in context.clone() {
            let text = value.as_ref().to_string();
            let _: RestrictedExpression = text.parse().unwrap_or_else(|e| {
                panic!(
                    "Context value for key `{key}` cannot be printed and parsed:\n\
                     {value:?}\nParse error: {e}"
                )
            });
        }
    }
}

/// A [`PolicySet`] should serialize to JSON and deserialize again. This function panics for
/// inputs where it does not.
pub fn policyset_to_json_deserializes(original: PolicySet) -> PolicySet {
    let json = original
        .to_json()
        .unwrap_or_else(|e| panic!("PolicySet could not be serialized to JSON.\nError: {e:?}"));
    PolicySet::from_json_value(json.clone()).unwrap_or_else(|e| {
        panic!("JSON from PolicySet failed to deserialize.\nJSON: {json}\nError: {e:?}")
    })
}

/// A [`Schema`] should serialize to JSON and deserialize again. Panics if serializing or
/// deserializing fails.
/// Caller should use the result if they need to assert equality with the input.
pub fn schema_to_json_deserializes(schema: &Schema) -> Schema {
    let validator_schema: &ValidatorSchema = schema.as_ref();
    let fragment = validator_schema
        .to_json_schema()
        .expect("ValidatorSchema could not be converted to JSON schema fragment");
    let json = serde_json::to_value(&fragment)
        .unwrap_or_else(|e| panic!("Schema fragment could not be serialized to JSON.\nError: {e}"));
    Schema::from_json_value(json.clone()).unwrap_or_else(|e| {
        panic!("JSON from Schema failed to re-parse.\nJSON: {json}\nError: {e}")
    })
}

/// A [`Schema`] should print to Cedar syntax and then parse again. Panics if printing or parsing
/// fails.
/// Caller should use the result if they need to assert equality with the input.
pub fn schema_to_cedar_parses(schema: &Schema) -> Schema {
    let validator_schema: &ValidatorSchema = schema.as_ref();
    let cedar_text = validator_schema
        .to_cedar_schema()
        .expect("Schema fragment could not be converted to Cedar schema syntax");
    Schema::from_cedarschema_str(&cedar_text)
        .unwrap_or_else(|e| {
            panic!("Cedar schema text failed to re-parse.\nText: {cedar_text}\nError: {e}")
        })
        .0
}
