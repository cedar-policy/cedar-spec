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
use cedar_lean_ffi::{
    CedarLeanFfi, FfiError, LeanSchema, UncheckedPartialEntity, UncheckedPartialRequest,
    ValidationResponse,
};
use cedar_policy::pst::{Clause, Expr, UnaryOp};
use cedar_policy::{
    Context, Entities, Entity, EntityId, EntityUid, PartialEntities, PartialEntity,
    PartialEntityUid, PartialRequest, PolicyId, PolicySet, Request, RestrictedExpression, Schema,
    Validator,
};
use cedar_policy_core::ast::{self, Value};
use cedar_policy_core::extensions::Extensions;
use cedar_policy_core::tpe::residual::Residual;
use cedar_policy_generators::{
    abac::ABACRequest, hierarchy::HierarchyGenerator, schema, schema_gen::SchemaGen,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use ref_cast::RefCast;
use smol_str::SmolStr;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::convert::TryFrom;
use std::sync::Arc;

use crate::{abac, schemas};

/// Generates a schema and a hierarchy of entities for it, including its action entities.
pub fn arbitrary_schema_and_entities(
    settings: ABACSettings,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<(Schema, Entities)> {
    let generated_schema = schema::Schema::arbitrary(settings, u)?;
    let hierarchy = generated_schema.arbitrary_hierarchy(u)?;
    let schema =
        Schema::try_from(generated_schema).map_err(|_| arbitrary::Error::IncorrectFormat)?;
    let entities = schemas::add_actions_to_entities(
        &schema,
        Entities::try_from(hierarchy).map_err(|_| arbitrary::Error::NotEnoughData)?,
    )?;
    Ok((schema, entities))
}

/// Generates a schema and 8 requests for it.
pub fn arbitrary_schema_and_requests(
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<(Schema, [ABACRequest; 8])> {
    let generated_schema = schema::Schema::arbitrary(ABACSettings::undirected(), u)?;
    let hierarchy = generated_schema.arbitrary_hierarchy(u)?;
    let requests = [
        generated_schema.arbitrary_request(&hierarchy, u)?,
        generated_schema.arbitrary_request(&hierarchy, u)?,
        generated_schema.arbitrary_request(&hierarchy, u)?,
        generated_schema.arbitrary_request(&hierarchy, u)?,
        generated_schema.arbitrary_request(&hierarchy, u)?,
        generated_schema.arbitrary_request(&hierarchy, u)?,
        generated_schema.arbitrary_request(&hierarchy, u)?,
        generated_schema.arbitrary_request(&hierarchy, u)?,
    ];
    let schema =
        Schema::try_from(generated_schema).map_err(|_| arbitrary::Error::IncorrectFormat)?;
    Ok((schema, requests))
}

/// Size hint for the inputs of [`arbitrary_schema_and_entities`].
pub fn schema_and_entities_size_hint(
    depth: usize,
) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
    Ok(arbitrary::size_hint::and_all(&[
        schema::Schema::arbitrary_size_hint(depth)?,
        HierarchyGenerator::size_hint(depth),
    ]))
}

/// Size hint for the inputs of [`arbitrary_schema_and_requests`].
pub fn schema_and_requests_size_hint(
    depth: usize,
) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
    Ok(arbitrary::size_hint::and_all(&[
        schema_and_entities_size_hint(depth)?,
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

fn to_restricted_exprs<'a>(
    pairs: impl Iterator<Item = (&'a SmolStr, &'a ast::PartialValue)>,
) -> BTreeMap<SmolStr, RestrictedExpression> {
    pairs
        .map(|(k, v)| {
            (
                k.clone(),
                ast::RestrictedExpr::from(Value::try_from(v.clone()).unwrap()).into(),
            )
        })
        .collect()
}

/// Builds a partial entity whose uid and ancestors come from `entity` and whose attributes
/// and tags come from `attrs_from`, which must have the same entity type as `entity`.
fn entity_to_partial_entity(
    entity: &Entity,
    attrs_from: &Entity,
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
            Some(to_restricted_exprs(attrs_from.as_ref().attrs()))
        },
        // We can only mark ancestors of leaf nodes to unknown
        if !is_action && leafs.contains(&entity.uid()) && u.ratio(1, 4)? {
            None
        } else {
            Some(HashSet::from_iter(
                entity.as_ref().ancestors().cloned().map(Into::into),
            ))
        },
        if !is_action && u.ratio(1, 4)? {
            None
        } else {
            Some(to_restricted_exprs(attrs_from.as_ref().tags()))
        },
        schema,
    )
    .map_err(|_| arbitrary::Error::IncorrectFormat)
}

// Reorders `sorted` so that each entity might be associated with another entity of the same type to
// take its attributes from. This functions doesn't actually change the attributes. That's done when
// building the final partial entity.
fn shuffle_within_entity_types<'a>(
    sorted: &[&'a Entity],
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<Vec<&'a Entity>> {
    sorted
        .iter()
        .enumerate()
        .map(|(i, e)| {
            if u.ratio(1, 2)? {
                Ok(*e)
            } else {
                Ok(sorted
                    .get(i + 1)
                    .filter(|next| next.uid().type_name() == e.uid().type_name())
                    .copied()
                    .unwrap_or(*e))
            }
        })
        .collect()
}

/// Constructs a `PartialEntities` given some concrete entities, using `u` to
/// arbitrarily choose some data to delete, making it unknown in subsequent
/// partial evaluation.
///
/// When `shuffle_attrs` is set each resulting partial entity may take its attributes from a different
/// entity of the same type. This way the entities are valid, but aren't consistent.
pub fn entities_to_partial_entities<'a>(
    entities: impl Iterator<Item = &'a Entity>,
    shuffle_attrs: bool,
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
    let partial_entities = if shuffle_attrs {
        // Sort for determinism: `HashSet` iteration order is unspecified
        let mut sorted: Vec<&Entity> = entities.iter().collect();
        sorted.sort_by_cached_key(|e| e.uid().to_string());
        sorted
            .iter()
            .zip(shuffle_within_entity_types(&sorted, u)?)
            .map(|(e, attrs_from)| entity_to_partial_entity(e, attrs_from, u, &leafs, schema))
            .collect::<arbitrary::Result<Vec<PartialEntity>>>()?
    } else {
        entities
            .iter()
            .map(|e| entity_to_partial_entity(e, e, u, &leafs, schema))
            .collect::<arbitrary::Result<Vec<PartialEntity>>>()?
    };
    PartialEntities::from_partial_entities(partial_entities, schema)
        .map_err(|_| arbitrary::Error::IncorrectFormat)
}

/// Input for TPE fuzz targets: an ABAC hierarchy, schema, and 8 associated partial requests.
#[derive(Debug, Clone)]
pub struct TpeFuzzTargetInput {
    pub abac_input: abac::FuzzTargetInput<true>,
    pub partial_requests: [PartialRequest; 8],
    pub partial_entities: PartialEntities,
}

fn maybe_eid(
    uid: &ast::EntityUID,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<PartialEntityUid> {
    Ok(PartialEntityUid::new(
        uid.entity_type().clone().into(),
        if u.ratio(1, 4)? {
            None
        } else {
            Some(EntityId::new(uid.eid()))
        },
    ))
}

/// Constructs a partial request that is not validated against any schema, taking the principal
/// and resource from `req` but the action and context from `action_from`. Mixing two requests
/// yields requests whose principal and resource types don't apply to the action, or whose
/// context doesn't match it.
pub fn make_unchecked_partial_request(
    req: &ABACRequest,
    action_from: &ABACRequest,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<UncheckedPartialRequest> {
    let ast::Context::Value(context) = &action_from.context else {
        // generated requests always have concrete contexts
        return Err(arbitrary::Error::IncorrectFormat);
    };
    Ok(UncheckedPartialRequest {
        principal: maybe_eid(&req.principal, u)?,
        action: action_from.action.clone().into(),
        resource: maybe_eid(&req.resource, u)?,
        context: if u.ratio(1, 4)? {
            None
        } else {
            Some(
                context
                    .iter()
                    .map(|(k, v)| (k.clone(), ast::RestrictedExpr::from(v.clone()).into()))
                    .collect(),
            )
        },
    })
}

pub fn entity_to_unchecked_partial_entity(
    entity: &Entity,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<UncheckedPartialEntity> {
    Ok(UncheckedPartialEntity {
        uid: entity.uid(),
        attrs: if u.ratio(1, 4)? {
            None
        } else {
            Some(to_restricted_exprs(entity.as_ref().attrs()))
        },
        ancestors: if u.ratio(1, 4)? {
            None
        } else {
            Some(HashSet::from_iter(
                entity.as_ref().ancestors().cloned().map(Into::into),
            ))
        },
        tags: if u.ratio(1, 4)? {
            None
        } else {
            Some(to_restricted_exprs(entity.as_ref().tags()))
        },
    })
}

/// Construct a partial request from a concrete request, randomly dropping eids.
pub fn make_partial_request(
    req: &ABACRequest,
    u: &mut Unstructured<'_>,
    schema: &Schema,
) -> arbitrary::Result<PartialRequest> {
    PartialRequest::new(
        maybe_eid(&req.principal, u)?,
        req.action.clone().into(),
        maybe_eid(&req.resource, u)?,
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
            entities_to_partial_entities(abac_input.entities.iter(), false, u, &schema)?;
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
    let evaluator = cedar_policy_core::evaluator::Evaluator::new(
        request.as_ref().clone(),
        entities.as_ref(),
        Extensions::all_available(),
    );
    let rust_val = evaluator.interpret(&expr, &HashMap::new());
    let rust_val = rust_val.as_ref().map_err(|_| ());

    let check = match ffi.check_reauthorize_residual(residual, request, entities, rust_val) {
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

/// Panics unless Lean agrees with `rust_passed`. `detail` is only formatted on failure.
fn assert_lean_agrees(
    check: &str,
    rust_passed: bool,
    lean: &ValidationResponse,
    detail: impl FnOnce() -> String,
) {
    assert_eq!(
        rust_passed,
        lean == &ValidationResponse::Ok(()),
        "{check} mismatch\nLean: {lean:?}\n{}",
        detail()
    );
}

/// Check that Rust and Lean agree on whether `entities` are valid for `schema`.
pub fn test_partial_entity_validation_equiv(
    ffi: &CedarLeanFfi,
    schema: &Schema,
    lean_schema: LeanSchema,
    entities: &[UncheckedPartialEntity],
) {
    // `PartialEntity::new` validates; unlike `PartialEntities::from_partial_entities` it
    // does not additionally compute the transitive closure, which Lean does not model.
    let rust_err = entities.iter().find_map(|e| {
        PartialEntity::new(
            e.uid.clone(),
            e.attrs.clone(),
            e.ancestors.clone(),
            e.tags.clone(),
            schema,
        )
        .err()
    });
    let lean_res = ffi
        .validate_partial_entities(lean_schema, entities)
        .expect("failed to execute partial entity validation");
    assert_lean_agrees(
        "partial entity validation",
        rust_err.is_none(),
        &lean_res,
        || format!("Rust: {rust_err:?}\nEntities: {entities:?}"),
    );
}

/// Check that Rust and Lean agree on whether `partial_entities` are consistent with `entities`.
pub fn test_partial_entity_consistency_equiv(
    ffi: &CedarLeanFfi,
    entities: &Entities,
    partial_entities: &PartialEntities,
) {
    let rust_res = partial_entities
        .as_ref()
        .check_consistency(entities.as_ref());
    let lean_res = ffi
        .check_partial_entity_consistency(entities, partial_entities)
        .expect("failed to execute partial entity consistency check");
    assert_lean_agrees(
        "partial entity consistency",
        rust_res.is_ok(),
        &lean_res,
        || {
            format!(
                "Rust: {rust_res:?}\nPartial entities: {partial_entities:?}\nEntities: {}",
                entities.as_ref()
            )
        },
    );
}

/// Check that Rust and Lean agree on whether `request` is valid for `schema`.
pub fn test_partial_request_validation_equiv(
    ffi: &CedarLeanFfi,
    schema: &Schema,
    lean_schema: LeanSchema,
    request: &UncheckedPartialRequest,
) {
    let context = request.context.clone().map(|c| {
        Context::from_pairs(c.into_iter().map(|(k, v)| (k.to_string(), v)))
            .expect("context built from a concrete context should be valid")
    });
    let rust_res = PartialRequest::new(
        request.principal.clone(),
        request.action.clone(),
        request.resource.clone(),
        context,
        schema,
    );
    let lean_res = ffi
        .validate_partial_request(lean_schema, request)
        .expect("failed to execute partial request validation");
    assert_lean_agrees(
        "partial request validation",
        rust_res.is_ok(),
        &lean_res,
        || format!("Rust: {:?}\nRequest: {request:?}", rust_res.err()),
    );
}

/// Check that Rust and Lean agree on whether `partial_request` is consistent with `request`.
pub fn test_partial_request_consistency_equiv(
    ffi: &CedarLeanFfi,
    request: &Request,
    partial_request: &PartialRequest,
) {
    let rust_res = partial_request.as_ref().check_consistency(request.as_ref());
    let lean_res = ffi
        .check_partial_request_consistency(request, partial_request)
        .expect("failed to execute partial request consistency check");
    assert_lean_agrees(
        "partial request consistency",
        rust_res.is_ok(),
        &lean_res,
        || format!("Rust: {rust_res:?}\nPartial request: {partial_request:?}\nRequest: {request}"),
    );
}
