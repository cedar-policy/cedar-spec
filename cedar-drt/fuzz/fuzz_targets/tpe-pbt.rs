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
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::fuzz_target;
use cedar_policy_core::{
    ast::{self, EntityUID, Expr, Request, RequestSchema, Value},
    entities::Entities,
    evaluator::Evaluator,
    extensions::Extensions,
    tpe::{
        entities::{PartialEntities, PartialEntity},
        is_authorized,
        request::{PartialEntityUID, PartialRequest},
    },
    validator::{CoreSchema, ValidationMode, Validator, ValidatorSchema},
};
use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    hierarchy::{Hierarchy, HierarchyGenerator},
    schema::Schema,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::convert::TryFrom;

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
    pub partial_entities: PartialEntities,
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
    Ok(PartialRequest::new_unchecked(
        PartialEntityUID {
            ty: req.principal.entity_type().clone(),
            eid: if u.ratio(1, 4)? {
                None
            } else {
                Some(req.principal.eid().clone())
            },
        },
        PartialEntityUID {
            ty: req.resource.entity_type().clone(),
            eid: if u.ratio(1, 4)? {
                None
            } else {
                Some(req.resource.eid().clone())
            },
        },
        req.action.clone(),
        None,
    ))
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
            .collect::<arbitrary::Result<Vec<_>>>()?
            .try_into()
            .unwrap();
        Ok(Self {
            schema,
            hierarchy: hierarchy.clone(),
            policy,
            requests,
            partial_requests,
            partial_entities: entities_to_partial_entities(hierarchy.entities(), u)?,
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

fn entity_to_partial_entity(
    entity: &ast::Entity,
    u: &mut Unstructured<'_>,
    leafs: &HashSet<EntityUID>,
) -> arbitrary::Result<PartialEntity> {
    Ok(PartialEntity {
        uid: entity.uid().clone(),
        attrs: if u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.attrs().map(|(k, v)| {
                (k.clone(), Value::try_from(v.clone()).unwrap())
            })))
        },
        ancestors: if leafs.contains(entity.uid()) {
            if u.ratio(1, 4)? {
                None
            } else {
                Some(HashSet::from_iter(entity.ancestors().cloned()))
            }
        } else {
            Some(HashSet::from_iter(entity.ancestors().cloned()))
        },
        tags: if u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.tags().map(|(k, v)| {
                (k.clone(), Value::try_from(v.clone()).unwrap())
            })))
        },
    })
}

fn entities_to_partial_entities<'a>(
    entities: impl Iterator<Item = &'a ast::Entity>,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<PartialEntities> {
    let entities: HashSet<ast::Entity> = HashSet::from_iter(entities.cloned());
    let mut leafs: HashSet<_> = entities.iter().map(|e| e.uid().clone()).collect();
    for e in &entities {
        for a in e.ancestors() {
            leafs.remove(a);
        }
    }
    Ok(PartialEntities::from_entities_unchecked(
        entities
            .iter()
            .map(|e| Ok((e.uid().clone(), entity_to_partial_entity(e, u, &leafs)?)))
            .collect::<arbitrary::Result<Vec<(ast::EntityUID, PartialEntity)>>>()?
            .into_iter(),
    ))
}

fn test_weak_equiv(residual: &Expr, e: &Expr, req: &Request, entities: &Entities) -> bool {
    let eval = Evaluator::new(req.clone(), entities, Extensions::all_available());
    let slots = HashMap::new();

    debug!("request: {req}");
    debug!("expr: {e}");
    debug!("residual: {residual}");
    let concrete_res = eval.interpret(e, &slots);
    let reeval_res = eval.interpret(&residual, &slots);
    debug!("concrete evaluation result: {concrete_res:?}");
    debug!("re-evaluation result: {reeval_res:?}");
    concrete_res.ok() == reeval_res.ok()
}

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    // preserve the schema in string format, which may be needed for error messages later
    let schemafile_string = input.schema.schemafile_string();
    if let Ok(schema) = ValidatorSchema::try_from(input.schema) {
        debug!("Schema: {schemafile_string}");
        if let Ok(entities) = Entities::try_from(input.hierarchy.clone()) {
            let validator = Validator::new(schema.clone());
            let mut policyset = ast::PolicySet::new();
            let policy: ast::StaticPolicy = input.policy.into();
            policyset.add_static(policy.clone()).unwrap();
            let passes_strict = passes_policy_validation(&validator, &policyset);
            if passes_strict {
                for e in input.partial_entities.entities() {
                    e.validate(&schema).expect("entities should be valid");
                }
                let mut partial_entities = input.partial_entities;
                partial_entities
                    .compute_tc()
                    .expect("tc computation failed");
                let expr = policy.condition();
                for (request, partial_request) in
                    input.requests.into_iter().zip(input.partial_requests)
                {
                    let request: ast::Request = request.into();
                    if passes_request_validation(&schema, &request) {
                        let response =
                            is_authorized(&policyset, &partial_request, &partial_entities, &schema)
                                .expect("tpe failed");
                        assert!(test_weak_equiv(
                            &response.residual_policies()[0].condition(),
                            &expr,
                            &request,
                            &entities
                        ));
                    }
                }
            }
        }
    }
});
