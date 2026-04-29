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
use cedar_drt_inner::{
    fuzz_target,
    tpe::{TpeFuzzTargetInput, passes_policyset_validation, passes_request_validation},
};
use cedar_policy::{Authorizer, Entities, PolicySet, Request, Schema, Validator};
use log::debug;
use std::convert::TryFrom;

fn test_weak_equiv(
    residual: &PolicySet,
    e: &PolicySet,
    req: &Request,
    entities: &Entities,
) -> bool {
    debug!("request: {req}");
    debug!("expr: {e}");
    debug!("residual: {residual}");
    let authorizer = Authorizer::new();
    let concrete_res = authorizer.is_authorized(req, e, entities);
    let reeval_res = authorizer.is_authorized(req, residual, entities);
    debug!("concrete evaluation result: {concrete_res:?}");
    debug!("re-evaluation result: {reeval_res:?}");
    concrete_res.decision() == reeval_res.decision()
}

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: TpeFuzzTargetInput| {
    initialize_log();
    // preserve the schema in string format, which may be needed for error messages later
    let schemafile_string = input.abac_input.schema.schemafile_string();
    if let Ok(schema) = Schema::try_from(input.abac_input.schema) {
        debug!("Schema: {schemafile_string}");
        let validator = Validator::new(schema.clone());
        let policyset = input.abac_input.policy.into_policy_set();
        let passes_strict = passes_policyset_validation(&validator, &policyset);
        if passes_strict {
            let partial_entities = input.partial_entities;
            for (request, partial_request) in input
                .abac_input
                .requests
                .into_iter()
                .zip(input.partial_requests)
            {
                let request: Request = request.into();
                if passes_request_validation(&validator, &request) {
                    let response = policyset
                        .tpe(&partial_request, &partial_entities, &schema)
                        .expect("tpe failed");
                    assert!(test_weak_equiv(
                        &PolicySet::from_policies(response.residual_policies()).unwrap(),
                        &policyset,
                        &request,
                        &input.abac_input.entities
                    ));
                }
            }
        }
    }
});
