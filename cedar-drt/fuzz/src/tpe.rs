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

//! Test utilities for type-directed partial evaluation fuzz targets

use cedar_drt::tests::drop_some_entities;
use cedar_lean_ffi::{CedarLeanFfi, FfiError};
use cedar_policy::pst::{Clause, Expr, UnaryOp};
use cedar_policy::{
    Entities, Entity, EntityId, EntityUid, PartialEntities, PartialEntity, PartialEntityUid,
    PartialRequest, PolicyId, PolicySet, Request, Schema, Validator,
};
use cedar_policy_core::ast::{self, Value};
use cedar_policy_core::tpe::residual::Residual;
use cedar_policy_generators::abac::ABACRequest;
use cedar_policy_generators::hierarchy::HierarchyGenerator;
use cedar_policy_generators::schema;
use cedar_policy_generators::schema_gen::SchemaGen;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use ref_cast::RefCast;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::convert::TryFrom;
use std::sync::Arc;

use crate::abac;

fn entity_to_partial_entity(
    entity: &Entity,
    u: &mut Unstructured<'_>,
    leafs: &HashSet<EntityUid>,
    schema: &Schema,
) -> arbitrary::Result<PartialEntity> {
    let is_action = entity.uid().type_name().as_ref().is_action();
    PartialEntity::new(
        entity.as_ref().uid().clone().into(),
        if !is_action && u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.as_ref().attrs().map(
                |(k, v)| {
                    (
                        k.clone(),
                        ast::RestrictedExpr::from(Value::try_from(v.clone()).unwrap()).into(),
                    )
                },
            )))
        },
        // We can only mark ancestors of leaf nodes to unknown
        if !is_action && leafs.contains(&entity.uid()) {
            if u.ratio(1, 4)? {
                None
            } else {
                Some(HashSet::from_iter(
                    entity.as_ref().ancestors().cloned().map(Into::into),
                ))
            }
        } else {
            Some(HashSet::from_iter(
                entity.as_ref().ancestors().cloned().map(Into::into),
            ))
        },
        if !is_action && u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.as_ref().tags().map(|(k, v)| {
                (
                    k.clone(),
                    ast::RestrictedExpr::from(Value::try_from(v.clone()).unwrap()).into(),
                )
            })))
        },
        schema,
    )
    .map_err(|_| arbitrary::Error::IncorrectFormat)
}

/// Constructs a `PartialEntities` given some concrete entities, using `u` to
/// arbitrarily choose some data to delete, making it unknown in subsequent
/// partial evaluation.
pub fn entities_to_partial_entities<'a>(
    entities: impl Iterator<Item = &'a Entity>,
    u: &mut Unstructured<'_>,
    schema: &Schema,
) -> arbitrary::Result<PartialEntities> {
    let entities: HashSet<Entity> = HashSet::from_iter(entities.cloned());
    let mut leafs: HashSet<_> = entities.iter().map(|e| e.uid().clone()).collect();
    for e in &entities {
        for a in e.as_ref().ancestors() {
            leafs.remove(RefCast::ref_cast(a));
        }
    }
    PartialEntities::from_partial_entities(
        entities
            .iter()
            .map(|e| entity_to_partial_entity(e, u, &leafs, schema))
            .collect::<arbitrary::Result<Vec<PartialEntity>>>()?,
        schema,
    )
    .map_err(|_| arbitrary::Error::IncorrectFormat)
}

/// Input for TPE fuzz targets: an ABAC hierarchy, schema, and 8 associated partial requests.
#[derive(Debug, Clone)]
pub struct TpeFuzzTargetInput {
    pub abac_input: abac::FuzzTargetInput<true>,
    pub partial_requests: [PartialRequest; 8],
    pub partial_entities: PartialEntities,
}

/// Construct a partial request from a concrete request, randomly dropping eids.
pub fn make_partial_request(
    req: &ABACRequest,
    u: &mut Unstructured<'_>,
    schema: &Schema,
) -> arbitrary::Result<PartialRequest> {
    PartialRequest::new(
        PartialEntityUid::new(
            req.principal.entity_type().clone().into(),
            if u.ratio(1, 4)? {
                None
            } else {
                Some(EntityId::new(req.principal.eid()))
            },
        ),
        req.action.clone().into(),
        PartialEntityUid::new(
            req.resource.entity_type().clone().into(),
            if u.ratio(1, 4)? {
                None
            } else {
                Some(EntityId::new(req.resource.eid()))
            },
        ),
        None,
        schema,
    )
    .map_err(|_| arbitrary::Error::IncorrectFormat)
}

impl<'a> Arbitrary<'a> for TpeFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let abac_input = abac::FuzzTargetInput::<true>::arbitrary(u)?;
        let schema: Schema = abac_input
            .schema
            .clone()
            .try_into()
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        let partial_requests = abac_input
            .requests
            .iter()
            .map(|req| make_partial_request(req, u, &schema))
            .collect::<arbitrary::Result<Vec<_>>>()?
            .try_into()
            .unwrap();
        let partial_entities =
            entities_to_partial_entities(abac_input.entities.iter(), u, &schema)?;
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

/// A schema, a hierarchy, and eight (request, residual) pairs.
#[derive(Debug, Clone)]
pub struct TpeResidualFuzzTargetInput {
    pub entities: Entities,
    pub residual: Residual,
    pub reqs: [ABACRequest; 8],
}

impl<'a> Arbitrary<'a> for TpeResidualFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let settings = abac::FuzzTargetInput::<true>::settings();
        let gen_schema = schema::Schema::arbitrary(settings.clone(), u)?;
        let hierarchy = gen_schema.arbitrary_hierarchy(u)?;
        let reqs = [
            gen_schema.arbitrary_request(&hierarchy, u)?,
            gen_schema.arbitrary_request(&hierarchy, u)?,
            gen_schema.arbitrary_request(&hierarchy, u)?,
            gen_schema.arbitrary_request(&hierarchy, u)?,
            gen_schema.arbitrary_request(&hierarchy, u)?,
            gen_schema.arbitrary_request(&hierarchy, u)?,
            gen_schema.arbitrary_request(&hierarchy, u)?,
            gen_schema.arbitrary_request(&hierarchy, u)?,
        ];
        let residual = gen_schema
            .exprgenerator(Some(&hierarchy))
            .generate_residual(settings.max_depth, u)?;

        let entities = drop_some_entities(
            Entities::try_from(hierarchy).map_err(|_| arbitrary::Error::NotEnoughData)?,
            u,
        )?;
        Ok(Self {
            entities,
            reqs,
            residual,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}

/// Compare Rust and the model on reauthorizing an arbitrary residual against concrete data.
pub fn test_tpe_reauthorize_residual_equiv(
    ffi: &CedarLeanFfi,
    residual: &Residual,
    request: &Request,
    entities: &Entities,
) {
    let expr = ast::Expr::from(residual.clone());
    let core_entities: &cedar_policy_core::entities::Entities = entities.as_ref();
    let evaluator = cedar_policy_core::evaluator::Evaluator::new(
        request.as_ref().clone(),
        core_entities,
        cedar_policy_core::extensions::Extensions::all_available(),
    );
    let rust = evaluator.interpret(&expr, &std::collections::HashMap::new());
    let expected = rust.as_ref().map_err(|_| ());

    let check = match ffi.check_reauthorize_residual(residual, request, entities, expected) {
        Ok(c) => c,
        Err(FfiError::LeanBackendError(e)) => {
            debug!("{e}");
            return;
        }
        Err(e) => panic!("Unexpected FfiError: {e:?}"),
    };
    assert!(
        check.agrees,
        "arbitrary-residual reauthorization mismatch\n\
         input: {residual:?}\n\
         Rust:  {}\n\
         Lean:  {}",
        check.expected, check.actual
    );
}

/// Whether a policyset passes strict validation.
pub fn passes_policyset_validation(validator: &Validator, pset: &PolicySet) -> bool {
    validator
        .validate(pset, cedar_policy::ValidationMode::Strict)
        .validation_passed()
}

/// Whether a request passes validation against the validator's schema.
pub fn passes_request_validation(validator: &Validator, request: &Request) -> bool {
    Request::new(
        request.principal().unwrap().clone(),
        request.action().unwrap().clone(),
        request.resource().unwrap().clone(),
        request.context().unwrap().clone(),
        Some(validator.schema()),
    )
    .is_ok()
}

/// Compare Rust and Lean TPE outputs for a single partial request.
pub fn test_tpe_is_authorized_equiv(
    ffi: &CedarLeanFfi,
    schema: &Schema,
    policies: &PolicySet,
    partial_request: &PartialRequest,
    partial_entities: &PartialEntities,
) {
    // Run Rust TPE
    let maybe_rust_resp = policies.tpe(partial_request, partial_entities, schema);

    // Run Lean TPE
    let maybe_lean_resp =
        ffi.is_authorized_partial(policies, partial_request, partial_entities, schema);

    let (rust_resp, lean_resp) = match (maybe_rust_resp, maybe_lean_resp) {
        (Ok(r), Ok(l)) => (r, l),
        (Ok(r), Err(e)) => panic!(
            "Got Lean TPE error, but Rust returned response.\nRust: {:?}\n, Lean: {}",
            r, e
        ),
        (Err(e), Ok(l)) => panic!(
            "Got Rust TPE error, but Lean returned response.\nRust: {}\n, Lean: {:?}",
            e, l
        ),
        // LeanBackendError is returned for expected error conditions like ill-typed policies
        (Err(_), Err(FfiError::LeanBackendError(_))) => return,
        // other FfiError variants indicate a bug in the FFI layer
        (Err(_), Err(e)) => panic!("Unexpected FfiError: {e:?}"),
    };

    // Compare decisions
    assert_eq!(
        rust_resp.decision(),
        lean_resp.decision,
        "TPE decision mismatch"
    );

    // Compare policy categorizations (comparing sets of policy IDs)
    fn to_set<'a>(iter: impl Iterator<Item = &'a PolicyId> + 'a) -> HashSet<PolicyId> {
        iter.cloned().collect::<HashSet<_>>()
    }
    // The satisfied forbids/permits match.
    assert_eq!(
        to_set(rust_resp.true_permits()),
        lean_resp.satisfied_permits,
        "satisfied_permits mismatch"
    );
    assert_eq!(
        to_set(rust_resp.true_forbids()),
        lean_resp.satisfied_forbids,
        "satisfied_forbids mismatch"
    );
    // False permits/forbids match
    assert_eq!(
        to_set(rust_resp.false_permits()),
        lean_resp.false_permits,
        "false_permits mismatch"
    );
    assert_eq!(
        to_set(rust_resp.false_forbids()),
        lean_resp.false_forbids,
        "false_forbids mismatch"
    );
    // Error permits/forbids match
    assert_eq!(
        to_set(rust_resp.error_permits()),
        lean_resp.error_permits,
        "error_permits mismatch"
    );
    assert_eq!(
        to_set(rust_resp.error_forbids()),
        lean_resp.error_forbids,
        "error_forbids mismatch"
    );
    // The policies with residuals match on both sides.
    assert_eq!(
        to_set(rust_resp.residual_permits()),
        lean_resp.residual_permits,
        "residual_permits mismatch"
    );
    assert_eq!(
        to_set(rust_resp.residual_forbids()),
        lean_resp.residual_forbids,
        "residual_forbids mismatch"
    );

    // Compare residual expressions by policy ID via PST
    let rust_residual_map: HashMap<PolicyId, Expr> = rust_resp
        .policies()
        .map(|rp| {
            let pst = rp
                .to_pst()
                .expect("policy->pst conversion should succeed for residuals");
            // Residual should have exactly one clause
            let clause = match pst.body().clauses().as_slice() {
                [Clause::When(x)] => x.clone(),
                [Clause::Unless(x)] => Arc::new(Expr::UnaryOp {
                    op: UnaryOp::Not,
                    expr: x.clone(),
                }),
                _ => panic!("zero or multiple when/unless clauses in residual policy"),
            };
            (rp.id().clone(), Arc::unwrap_or_clone(clause))
        })
        .collect();

    for lean_rp in &lean_resp.residuals {
        let lean_pst = Expr::try_from(lean_rp.residual.clone())
            .expect("lean residual->pst conversion should succeed");
        let rust_pst = rust_residual_map.get(&lean_rp.id).unwrap_or_else(|| {
            panic!(
                "Lean returned residual for policy {:?} but Rust did not.\n\
                 Rust residual IDs: {:?}",
                lean_rp.id,
                rust_residual_map.keys().collect::<Vec<_>>()
            )
        });
        assert_eq!(
            rust_pst, &lean_pst,
            "Residual expression mismatch for policy {:?}\n\
             Rust PST: {rust_pst:?}\nLean PST: {lean_pst:?}",
            lean_rp.id,
        );
    }
}
