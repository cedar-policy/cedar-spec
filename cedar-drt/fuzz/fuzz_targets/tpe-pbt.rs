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
use cedar_drt_inner::{abac, fuzz_target, tpe::entities_to_partial_entities};
use cedar_policy::Entities;
use cedar_policy_core::{
    ast::{self, Expr, Request, RequestSchema},
    evaluator::Evaluator,
    extensions::Extensions,
    tpe::{
        entities::PartialEntities,
        is_authorized,
        request::{PartialEntityUID, PartialRequest},
    },
    validator::{CoreSchema, ValidationMode, Validator, ValidatorSchema},
};
use cedar_policy_generators::abac::ABACRequest;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use std::collections::HashMap;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, schema, and 8 associated policies
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    pub abac_input: abac::FuzzTargetInput<true>,
    pub partial_requests: [PartialRequest; 8],
    pub partial_entities: PartialEntities,
}

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
        let abac_input = abac::FuzzTargetInput::<true>::arbitrary(u)?;
        let partial_requests = abac_input
            .requests
            .iter()
            .map(|req| make_partial_request(req, u))
            .collect::<arbitrary::Result<Vec<_>>>()?
            .try_into()
            .unwrap();
        let partial_entities = entities_to_partial_entities(abac_input.entities.iter(), u)?;
        Ok(Self {
            abac_input,
            partial_requests,
            partial_entities,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        abac::FuzzTargetInput::<true>::try_size_hint(depth)
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

fn test_weak_equiv(residual: &Expr, e: &Expr, req: &Request, entities: &Entities) -> bool {
    let eval = Evaluator::new(req.clone(), entities.as_ref(), Extensions::all_available());
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
    let schemafile_string = input.abac_input.schema.schemafile_string();
    if let Ok(schema) = ValidatorSchema::try_from(input.abac_input.schema) {
        debug!("Schema: {schemafile_string}");
        let validator = Validator::new(schema.clone());
        let mut policyset = ast::PolicySet::new();
        let policy: ast::StaticPolicy = input.abac_input.policy.into();
        policyset.add_static(policy.clone()).unwrap();
        let passes_strict = passes_policy_validation(&validator, &policyset);
        if passes_strict {
            for e in input.partial_entities.entities() {
                e.validate(&schema)
                    .unwrap_or_else(|_| panic!("entities should be valid: {e:#?}"));
            }
            let mut partial_entities = input.partial_entities;
            partial_entities
                .compute_tc()
                .expect("tc computation failed");
            let expr = policy.condition();
            for (request, partial_request) in input
                .abac_input
                .requests
                .into_iter()
                .zip(input.partial_requests)
            {
                let request: ast::Request = request.into();
                if passes_request_validation(&schema, &request) {
                    let response =
                        is_authorized(&policyset, &partial_request, &partial_entities, &schema)
                            .expect("tpe failed");
                    assert!(test_weak_equiv(
                        &cedar_policy_core::ast::Policy::from(
                            response.residual_policies().next().unwrap().clone()
                        )
                        .condition(),
                        &expr,
                        &request,
                        &input.abac_input.entities
                    ));
                }
            }
        }
    }
});
