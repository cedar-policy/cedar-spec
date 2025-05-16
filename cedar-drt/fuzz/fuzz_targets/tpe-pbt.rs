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
use cedar_drt::ast::Value;
use cedar_drt::extensions::Extensions;
use cedar_drt::initialize_log;
use cedar_drt_inner::*;
use cedar_partial_evaluation::entities::{PartialEntities, PartialEntity};
use cedar_partial_evaluation::request::{PartialEntityUID, PartialRequest};
use cedar_partial_evaluation::tpe::tpe_policy;
use cedar_policy_core::ast;
use cedar_policy_core::ast::RequestSchema;
use cedar_policy_core::authorizer::{AuthorizationError, Authorizer};
use cedar_policy_core::entities::Entities;
use cedar_policy_core::evaluator::EvaluationError;
use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    hierarchy::{Hierarchy, HierarchyGenerator},
    schema::Schema,
    settings::ABACSettings,
};
use cedar_policy_validator::{CoreSchema, ValidationMode, Validator, ValidatorSchema};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use std::collections::{BTreeMap, HashMap};
use std::convert::TryFrom;
use std::sync::Arc;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, schema, and 8 associated policies
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// generated hierarchy
    pub hierarchy: Hierarchy,
    /// the policy which we will see if it validates
    pub policy: ABACPolicy,
    /// the requests to try, if the policy validates.
    /// We try 8 requests per validated policy.
    pub requests: [ABACRequest; 8],
    pub partial_requests: [PartialRequest; 8],
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: true,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
};

fn make_partial_request(
    req: &ABACRequest,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<PartialRequest> {
    Ok(PartialRequest {
        principal: PartialEntityUID {
            ty: req.principal.entity_type().clone(),
            eid: if u.ratio(1, 4)? {
                None
            } else {
                Some(req.principal.eid().clone())
            },
        },
        action: req.action.clone(),
        resource: PartialEntityUID {
            ty: req.resource.entity_type().clone(),
            eid: if u.ratio(1, 4)? {
                None
            } else {
                Some(req.resource.eid().clone())
            },
        },
        context: None,
    })
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        let requests = [
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
        ];
        let partial_requests = requests
            .iter()
            .map(|req| make_partial_request(req, u))
            .collect()?;
        Ok(Self {
            schema,
            hierarchy,
            policy,
            requests,
            partial_requests,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}

/// helper function that just tells us whether a policyset passes validation
fn passes_policy_validation(validator: &Validator, policyset: &ast::PolicySet) -> bool {
    validator
        .validate(policyset, ValidationMode::Strict)
        .validation_passed()
}

fn passes_request_validation(schema: &ValidatorSchema, request: &ast::Request) -> bool {
    let core_schema = CoreSchema::new(schema);
    core_schema
        .validate_request(request, Extensions::all_available())
        .is_ok()
}

fn entity_to_partial_entity(entity: &ast::Entity) -> PartialEntity {
    PartialEntity {
        uid: PartialEntityUID {
            ty: entity.ty().clone(),
            eid: None,
        },
        attrs: Some(BTreeMap::from_iter(entity.attrs().map(|(k, v)| (k.clone(), Value::try_from(v.clone()).unwrap())))),
        ancestors: Some(HashSet::from_iter(entity.ancestors().cloned())),
        tags: Some(BTreeMap::from_iter(entity.tags().map(|(k, v)| (k.clone(), Value::try_from(v.clone()).unwrap())))),
    }
}

fn entities_to_partial_entities(entities: &Entities) -> PartialEntities {
    PartialEntities { entities: HashMap::from_iter(entities.entities().map(|(eid, entity)| (eid.clone(), entity_to_partial_entity(entity)))) }
}

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    // preserve the schema in string format, which may be needed for error messages later
    let schemafile_string = input.schema.schemafile_string();
    if let Ok(schema) = ValidatorSchema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
        if let Ok(entities) = Entities::try_from(input.hierarchy.clone()) {
            let validator = Validator::new(schema);
            let mut policyset = ast::PolicySet::new();
            let policy: ast::StaticPolicy = input.policy.into();
            policyset.add_static(policy.clone()).unwrap();
            let passes_strict = passes_policy_validation(&validator, &policyset);
            if passes_strict {
                let mut partial_entities = entities_to_partial_entities(&entities);
                partial_entities.compute_tc().expect("tc computation failed");
                for i in 0..8 {
                    let request: ast::Request = input.requests[i].into();
                    let partial_request = input.partial_requests[i];
                    if passes_request_validation(&schema, &request) {
                        let residual = tpe_policy(&policy.into(), &partial_request, &mut partial_entities, &schema, TCComputation::AlreadyComputed).expect("tpe failed");
                    }
                }
            }
        }
    }
});
