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
use cedar_policy::{
    Entities, Expression, Policy, PolicySet, Request, RequestEnv, Schema, ValidationMode,
};
use smol_str::SmolStr;

use crate::datatypes;

pub(crate) mod proto {
    #![allow(missing_docs)]
    include!(concat!(env!("OUT_DIR"), "/cedar_proto_ffi.rs"));
}

/// Serialize a Cedar Policy to a Protobuf message (note this is a custom Policy format that differs from cedar_policy::proto::Policy)
impl From<&Policy> for proto::Policy {
    fn from(policy: &Policy) -> Self {
        Self {
            template: Some(cedar_policy::proto::models::TemplateBody::from(
                policy.as_ref().template(),
            )),
            policy: Some(cedar_policy::proto::models::Policy::from(policy)),
        }
    }
}

/// Serialize a RequestEnv to a Protobuf message
impl From<&RequestEnv> for proto::RequestEnv {
    fn from(req_env: &RequestEnv) -> Self {
        Self {
            principal: Some(cedar_policy::proto::models::Name::from(req_env.principal())),
            action: Some(cedar_policy::proto::models::EntityUid::from(
                req_env.action(),
            )),
            resource: Some(cedar_policy::proto::models::Name::from(req_env.resource())),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CheckPolicyRequest {
    pub(crate) policy: Policy,
    pub(crate) request: RequestEnv,
}

impl proto::CheckPolicyRequest {
    pub(crate) fn new(policy: &Policy, request: &RequestEnv) -> Self {
        Self {
            policy: Some(proto::Policy::from(policy)),
            request: Some(proto::RequestEnv::from(request)),
        }
    }
}

/// Serialize the symcc request arguments to a ProtoBuf message
impl From<&CheckPolicyRequest> for proto::CheckPolicyRequest {
    fn from(req: &CheckPolicyRequest) -> Self {
        Self::new(&req.policy, &req.request)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CheckPolicySetRequest {
    pub(crate) policyset: PolicySet,
    pub(crate) request: RequestEnv,
}

impl proto::CheckPolicySetRequest {
    pub(crate) fn new(policyset: &PolicySet, request: &RequestEnv) -> Self {
        Self {
            policy_set: Some(cedar_policy::proto::models::PolicySet::from(policyset)),
            request: Some(proto::RequestEnv::from(request)),
        }
    }
}

/// Serialize the symcc request arguments to a ProtoBuf message
impl From<&CheckPolicySetRequest> for proto::CheckPolicySetRequest {
    fn from(req: &CheckPolicySetRequest) -> Self {
        Self::new(&req.policyset, &req.request)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ComparePoliciesRequest {
    pub(crate) src_policy: Policy,
    pub(crate) tgt_policy: Policy,
    pub(crate) request: RequestEnv,
}

impl proto::ComparePoliciesRequest {
    pub(crate) fn new(src_policy: &Policy, tgt_policy: &Policy, request: &RequestEnv) -> Self {
        Self {
            policy1: Some(proto::Policy::from(src_policy)),
            policy2: Some(proto::Policy::from(tgt_policy)),
            request: Some(proto::RequestEnv::from(request)),
        }
    }
}

/// Serialize the symcc request arguments to a ProtoBuf message
impl From<&ComparePoliciesRequest> for proto::ComparePoliciesRequest {
    fn from(req: &ComparePoliciesRequest) -> Self {
        Self::new(&req.src_policy, &req.tgt_policy, &req.request)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ComparePolicySetsRequest {
    pub(crate) src_policyset: PolicySet,
    pub(crate) tgt_policyset: PolicySet,
    pub(crate) request: RequestEnv,
}

impl proto::ComparePolicySetsRequest {
    pub(crate) fn new(
        src_policyset: &PolicySet,
        tgt_policyset: &PolicySet,
        request: &RequestEnv,
    ) -> Self {
        Self {
            src_policy_set: Some(cedar_policy::proto::models::PolicySet::from(src_policyset)),
            tgt_policy_set: Some(cedar_policy::proto::models::PolicySet::from(tgt_policyset)),
            request: Some(proto::RequestEnv::from(request)),
        }
    }
}

/// Serialize the symcc request arguments to a ProtoBuf message
impl From<&ComparePolicySetsRequest> for proto::ComparePolicySetsRequest {
    fn from(req: &ComparePolicySetsRequest) -> Self {
        Self::new(&req.src_policyset, &req.tgt_policyset, &req.request)
    }
}

/// Serialize an authorization request
impl proto::AuthorizationRequest {
    pub(crate) fn new(policyset: &PolicySet, entities: &Entities, request: &Request) -> Self {
        Self {
            request: Some(cedar_policy::proto::models::Request::from(request)),
            policies: Some(cedar_policy::proto::models::PolicySet::from(policyset)),
            entities: Some(cedar_policy::proto::models::Entities::from(entities)),
        }
    }
}

/// Serialize an Expression evaluation request (checked or unchecked)
impl proto::EvaluationRequestChecked {
    pub(crate) fn new(expr: &Expression, entities: &Entities, request: &Request) -> Self {
        Self {
            expr: Some(cedar_policy::proto::models::Expr::from(expr)),
            request: Some(cedar_policy::proto::models::Request::from(request)),
            entities: Some(cedar_policy::proto::models::Entities::from(entities)),
            expected: None,
        }
    }

    pub(crate) fn new_checked(
        expr: &Expression,
        entities: &Entities,
        request: &Request,
        expected: Option<&Expression>,
    ) -> Self {
        Self {
            expr: Some(cedar_policy::proto::models::Expr::from(expr)),
            request: Some(cedar_policy::proto::models::Request::from(request)),
            entities: Some(cedar_policy::proto::models::Entities::from(entities)),
            expected: expected.map(cedar_policy::proto::models::Expr::from),
        }
    }
}

/// Serialize a PolicySet validation request
impl proto::ValidationRequest {
    pub(crate) fn new(policyset: &PolicySet, schema: &Schema, mode: &ValidationMode) -> Self {
        // Use a custom code to do this so that this code will compile against any cedar-policy version >= 4.4.0
        let mode = match mode {
            ValidationMode::Strict => cedar_policy::proto::models::ValidationMode::Strict,
            _ => panic!("Lean Validator only supports strict validation"),
        };
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            policies: Some(cedar_policy::proto::models::PolicySet::from(policyset)),
            mode: mode.into(),
        }
    }
}

/// Serialize a PolicySet level-validation request
impl proto::LevelValidationRequest {
    pub(crate) fn new(policyset: &PolicySet, schema: &Schema, level: i32) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            policies: Some(cedar_policy::proto::models::PolicySet::from(policyset)),
            level,
        }
    }
}

/// Serialize an entities validation request
impl proto::EntityValidationRequest {
    pub(crate) fn new(schema: &Schema, entities: &Entities) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            entities: Some(cedar_policy::proto::models::Entities::from(entities)),
        }
    }
}

/// Serialize a request validation request
impl proto::RequestValidationRequest {
    pub(crate) fn new(schema: &Schema, request: &Request) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            request: Some(cedar_policy::proto::models::Request::from(request)),
        }
    }
}

pub mod tpe {
    use cedar_policy::{
        Entities, EntityUid, PartialEntities, PartialEntityUid, PartialRequest, PolicySet, Request,
        RestrictedExpression, Schema, proto::models as cedar_proto,
    };
    use cedar_policy_core::ast::{Expr, Value, ValueKind};
    use cedar_policy_core::tpe::value::{
        PartialAttribute as CorePartialAttribute, PartialRecord as CorePartialRecord,
        PartialValue as CorePartialValue,
    };
    use smol_str::SmolStr;
    use std::collections::{BTreeMap, HashMap, HashSet};

    use super::proto;

    /// Serialize a partial entity UID
    impl proto::PartialEntityUid {
        fn from_inner(peuid: &cedar_policy_core::tpe::request::PartialEntityUID) -> Self {
            Self {
                ty: Some(cedar_policy::proto::models::Name::from(&peuid.ty)),
                id: peuid.eid.as_ref().map(|e| e.as_ref().to_string()),
            }
        }
    }

    /// Serialize a partial authorization request
    impl proto::PartialAuthorizationRequest {
        pub(crate) fn new(
            schema: &Schema,
            request: &PartialRequest,
            entities: &PartialEntities,
            policies: &PolicySet,
        ) -> Self {
            Self {
                schema: Some(cedar_policy::proto::models::Schema::from(schema)),
                policies: Some(cedar_policy::proto::models::PolicySet::from(policies)),
                request: Some(proto::PartialRequest::from_inner(request.as_ref())),
                entities: Some(proto::PartialEntities::from_inner(entities.as_ref())),
            }
        }
    }

    impl proto::Residual {
        pub(crate) fn from_inner(r: &cedar_policy_core::tpe::residual::Residual) -> Self {
            use cedar_policy_core::ast::{BinaryOp, UnaryOp};
            use cedar_policy_core::tpe::residual::{Residual as R, ResidualKind as K};
            use proto::residual::Kind;

            let ty = Some(cedar_policy::proto::models::Type::from(r.ty()));
            let mut out = Self {
                ty,
                ..Default::default()
            };
            let child = |r: &cedar_policy_core::tpe::residual::Residual| Self::from_inner(r);
            match r {
                R::Concrete { value, .. } => {
                    out.set_kind(Kind::Val);
                    out.val = Some(cedar_policy::proto::models::Expr::from(
                        &cedar_policy_core::ast::Expr::from(value.clone()),
                    ));
                }
                R::Error(_) => out.set_kind(Kind::Error),
                R::Partial { kind, .. } => match kind {
                    K::Var(v) => {
                        out.set_kind(Kind::Var);
                        out.set_var(cedar_policy::proto::models::expr::Var::from(v));
                    }
                    K::If {
                        test_expr,
                        then_expr,
                        else_expr,
                    } => {
                        out.set_kind(Kind::Ite);
                        out.children = vec![child(test_expr), child(then_expr), child(else_expr)];
                    }
                    K::And { left, right } => {
                        out.set_kind(Kind::And);
                        out.children = vec![child(left), child(right)];
                    }
                    K::Or { left, right } => {
                        out.set_kind(Kind::Or);
                        out.children = vec![child(left), child(right)];
                    }
                    K::UnaryApp { op, arg } => {
                        out.set_kind(Kind::UnaryApp);
                        out.set_unary_op(match op {
                            UnaryOp::Not => cedar_policy::proto::models::expr::unary_app::Op::Not,
                            UnaryOp::Neg => cedar_policy::proto::models::expr::unary_app::Op::Neg,
                            UnaryOp::IsEmpty => {
                                cedar_policy::proto::models::expr::unary_app::Op::IsEmpty
                            }
                        });
                        out.children = vec![child(arg)];
                    }
                    K::BinaryApp { op, arg1, arg2 } => {
                        use cedar_policy::proto::models::expr::binary_app::Op as POp;
                        out.set_kind(Kind::BinaryApp);
                        out.set_binary_op(match op {
                            BinaryOp::Eq => POp::Eq,
                            BinaryOp::Less => POp::Less,
                            BinaryOp::LessEq => POp::LessEq,
                            BinaryOp::Add => POp::Add,
                            BinaryOp::Sub => POp::Sub,
                            BinaryOp::Mul => POp::Mul,
                            BinaryOp::In => POp::In,
                            BinaryOp::Contains => POp::Contains,
                            BinaryOp::ContainsAll => POp::ContainsAll,
                            BinaryOp::ContainsAny => POp::ContainsAny,
                            BinaryOp::GetTag => POp::GetTag,
                            BinaryOp::HasTag => POp::HasTag,
                        });
                        out.children = vec![child(arg1), child(arg2)];
                    }
                    K::GetAttr { expr, attr } => {
                        out.set_kind(Kind::GetAttr);
                        out.attr = attr.to_string();
                        out.children = vec![child(expr)];
                    }
                    K::HasAttr { expr, attr } => {
                        out.set_kind(Kind::HasAttr);
                        out.attr = attr.to_string();
                        out.children = vec![child(expr)];
                    }
                    K::Like { expr, pattern } => {
                        out.set_kind(Kind::Like);
                        out.pattern = pattern
                            .iter()
                            .map(cedar_policy::proto::models::expr::like::PatternElem::from)
                            .collect();
                        out.children = vec![child(expr)];
                    }
                    K::Is { expr, entity_type } => {
                        out.set_kind(Kind::Is);
                        out.entity_type =
                            Some(cedar_policy::proto::models::Name::from(entity_type.name()));
                        out.children = vec![child(expr)];
                    }
                    K::Set(items) => {
                        out.set_kind(Kind::Set);
                        out.children = items.iter().map(child).collect();
                    }
                    K::Record(attrs) => {
                        out.set_kind(Kind::Record);
                        out.field_names = attrs.keys().map(|k| k.to_string()).collect();
                        out.children = attrs.values().map(child).collect();
                    }
                    K::ExtensionFunctionApp { fn_name, args } => {
                        out.set_kind(Kind::Call);
                        out.fn_name = Some(cedar_policy::proto::models::Name::from(fn_name));
                        out.children = args.iter().map(child).collect();
                    }
                },
            }
            out
        }
    }

    /// Serialize a request to reauthorize an arbitrary residual against concrete data.
    impl proto::ResidualReauthorizationRequest {
        pub(crate) fn new(
            residual: &cedar_policy_core::tpe::residual::Residual,
            request: &Request,
            entities: &Entities,
            expected: Result<&cedar_policy_core::ast::Value, ()>,
        ) -> Self {
            Self {
                residual: Some(proto::Residual::from_inner(residual)),
                request: Some(cedar_policy::proto::models::Request::from(request)),
                entities: Some(cedar_policy::proto::models::Entities::from(entities)),
                expected_value: expected.ok().map(|v| {
                    cedar_policy::proto::models::Expr::from(&cedar_policy_core::ast::Expr::from(
                        v.clone(),
                    ))
                }),
                expects_error: expected.is_err(),
            }
        }
    }

    fn expr_from_partial_value(value: &CorePartialValue) -> Option<Expr> {
        match value {
            CorePartialValue::Lit(lit) => Some(Expr::from(Value::new(lit.clone(), None))),
            CorePartialValue::Set(set) => {
                Some(Expr::from(Value::new(ValueKind::Set(set.clone()), None)))
            }
            CorePartialValue::ExtensionValue(ext) => Some(Expr::from(Value::new(
                ValueKind::ExtensionValue(ext.clone()),
                None,
            ))),
            CorePartialValue::Record(record) => {
                let fields = partial_record_exprs(record)?;
                Expr::record(fields).ok()
            }
        }
    }

    /// Encode only records representable by the legacy concrete-value wire format.
    /// Returning `None` makes the entire component unknown, which is conservative.
    fn partial_record_exprs(record: &CorePartialRecord) -> Option<BTreeMap<SmolStr, Expr>> {
        record
            .attrs()
            .filter_map(|(key, state)| match state {
                CorePartialAttribute::Value(value) => {
                    Some(expr_from_partial_value(value).map(|expr| (key.clone(), expr)))
                }
                CorePartialAttribute::Absent => None,
                CorePartialAttribute::Exists | CorePartialAttribute::Unknown => Some(None),
            })
            .collect()
    }

    fn partial_record_to_proto(
        record: &CorePartialRecord,
    ) -> Option<HashMap<String, cedar_proto::Expr>> {
        Some(
            partial_record_exprs(record)?
                .into_iter()
                .map(|(key, expr)| (key.to_string(), cedar_proto::Expr::from(&expr)))
                .collect(),
        )
    }

    impl proto::PartialRequest {
        fn from_inner(req: &cedar_policy_core::tpe::request::PartialRequest) -> Self {
            let (context, has_context) = req
                .context()
                .and_then(partial_record_to_proto)
                .map_or_else(|| (Default::default(), false), |context| (context, true));
            Self {
                principal: Some(proto::PartialEntityUid::from_inner(req.principal())),
                action: Some(cedar_proto::EntityUid::from(req.action())),
                resource: Some(proto::PartialEntityUid::from_inner(req.resource())),
                context,
                has_context,
            }
        }
    }

    impl proto::PartialEntities {
        fn from_inner(entities: &cedar_policy_core::tpe::entities::PartialEntities) -> Self {
            Self {
                entities: entities
                    .entities()
                    .map(proto::PartialEntity::from_inner)
                    .collect(),
            }
        }
    }

    impl proto::PartialEntity {
        fn from_inner(entity: &cedar_policy_core::tpe::entities::PartialEntity) -> Self {
            let (attrs, has_attrs) = entity
                .attrs()
                .and_then(partial_record_to_proto)
                .map_or_else(|| (Default::default(), false), |attrs| (attrs, true));
            let (ancestors, has_ancestors) = entity.ancestors().map_or_else(
                || (Default::default(), false),
                |ancestors| {
                    (
                        ancestors.iter().map(cedar_proto::EntityUid::from).collect(),
                        true,
                    )
                },
            );
            let (tags, has_tags) = entity
                .tags()
                .and_then(partial_record_to_proto)
                .map_or_else(|| (Default::default(), false), |tags| (tags, true));
            Self {
                uid: Some(cedar_proto::EntityUid::from(entity.uid())),
                attrs,
                ancestors,
                tags,
                has_attrs,
                has_ancestors,
                has_tags,
            }
        }
    }

    /// A partial entity that has not been validated against any schema.
    ///
    /// All constructors of `PartialEntity` (for both the core and public types) enforce validation,
    /// so they cannot be used to build an invalid entity to send to Lean.
    #[derive(Debug, Clone)]
    pub struct UncheckedPartialEntity {
        pub uid: EntityUid,
        pub attrs: Option<BTreeMap<SmolStr, RestrictedExpression>>,
        pub ancestors: Option<HashSet<EntityUid>>,
        pub tags: Option<BTreeMap<SmolStr, RestrictedExpression>>,
    }

    /// A partial request that has not been validated against any schema.
    #[derive(Debug, Clone)]
    pub struct UncheckedPartialRequest {
        pub principal: PartialEntityUid,
        pub action: EntityUid,
        pub resource: PartialEntityUid,
        pub context: Option<BTreeMap<SmolStr, RestrictedExpression>>,
    }

    fn to_proto_exprs(
        m: &Option<BTreeMap<SmolStr, RestrictedExpression>>,
    ) -> HashMap<String, cedar_proto::Expr> {
        m.iter()
            .flatten()
            .map(|(k, v)| {
                let e = cedar_policy_core::ast::Expr::from(v.as_ref().clone());
                (k.to_string(), cedar_proto::Expr::from(&e))
            })
            .collect()
    }

    impl proto::PartialEntity {
        fn from_unchecked(entity: &UncheckedPartialEntity) -> Self {
            Self {
                uid: Some(cedar_proto::EntityUid::from(entity.uid.as_ref())),
                has_attrs: entity.attrs.is_some(),
                attrs: to_proto_exprs(&entity.attrs),
                has_ancestors: entity.ancestors.is_some(),
                ancestors: entity
                    .ancestors
                    .iter()
                    .flatten()
                    .map(|uid| cedar_proto::EntityUid::from(uid.as_ref()))
                    .collect(),
                has_tags: entity.tags.is_some(),
                tags: to_proto_exprs(&entity.tags),
            }
        }
    }

    impl proto::PartialRequest {
        fn from_unchecked(req: &UncheckedPartialRequest) -> Self {
            Self {
                principal: Some(proto::PartialEntityUid::from_inner(req.principal.as_ref())),
                action: Some(cedar_proto::EntityUid::from(req.action.as_ref())),
                resource: Some(proto::PartialEntityUid::from_inner(req.resource.as_ref())),
                has_context: req.context.is_some(),
                context: to_proto_exprs(&req.context),
            }
        }
    }

    /// Serialize a partial entity validation request
    impl proto::PartialEntityValidationRequest {
        pub(crate) fn new(entities: &[UncheckedPartialEntity]) -> Self {
            Self {
                entities: Some(proto::PartialEntities {
                    entities: entities
                        .iter()
                        .map(proto::PartialEntity::from_unchecked)
                        .collect(),
                }),
            }
        }
    }

    /// Serialize a partial entity consistency request
    impl proto::PartialEntityConsistencyRequest {
        pub(crate) fn new(entities: &Entities, partial_entities: &PartialEntities) -> Self {
            Self {
                entities: Some(cedar_proto::Entities::from(entities)),
                partial_entities: Some(proto::PartialEntities::from_inner(
                    partial_entities.as_ref(),
                )),
            }
        }
    }

    /// Serialize a partial request validation request
    impl proto::PartialRequestValidationRequest {
        pub(crate) fn new(request: &UncheckedPartialRequest) -> Self {
            Self {
                request: Some(proto::PartialRequest::from_unchecked(request)),
            }
        }
    }

    /// Serialize a partial request consistency request
    impl proto::PartialRequestConsistencyRequest {
        pub(crate) fn new(request: &Request, partial_request: &PartialRequest) -> Self {
            Self {
                request: Some(cedar_proto::Request::from(request)),
                partial_request: Some(proto::PartialRequest::from_inner(partial_request.as_ref())),
            }
        }
    }
}

impl proto::Uuf {
    pub(crate) fn new(uuf: &datatypes::Uuf) -> Self {
        Self {
            id: uuf.id.to_string(),
            arg: Some(proto::TermType::new(&uuf.arg)),
            out: Some(proto::TermType::new(&uuf.out)),
        }
    }
}

impl proto::ExtOp {
    pub(crate) fn new(ext_op: &datatypes::ExtOp) -> Self {
        match ext_op {
            datatypes::ExtOp::DecimalVal => Self::DecimalVal,
            datatypes::ExtOp::IPaddrIsV4 => Self::IPaddrIsV4,
            datatypes::ExtOp::IPaddrAddrV4 => Self::IPaddrAddrV4,
            datatypes::ExtOp::IPaddrPrefixV4 => Self::IPaddrPrefixV4,
            datatypes::ExtOp::IPaddrAddrV6 => Self::IPaddrAddrV6,
            datatypes::ExtOp::IPaddrPrefixV6 => Self::IPaddrPrefixV6,
            datatypes::ExtOp::DatetimeVal => Self::DatetimeVal,
            datatypes::ExtOp::DatetimeOfBitVec => Self::DatetimeOfBitVec,
            datatypes::ExtOp::DurationVal => Self::DurationVal,
            datatypes::ExtOp::DurationOfBitVec => Self::DurationOfBitVec,
        }
    }
}

impl proto::PatElem {
    pub(crate) fn new(elem: &datatypes::PatElem) -> Self {
        let elem = match elem {
            datatypes::PatElem::Star => proto::pat_elem::Elem::Star(true),
            datatypes::PatElem::Char { c } => proto::pat_elem::Elem::Char(*c),
        };
        Self { elem: Some(elem) }
    }
}

impl proto::Pattern {
    pub(crate) fn new(pattern: &[datatypes::PatElem]) -> Self {
        Self {
            pattern: pattern.iter().map(proto::PatElem::new).collect(),
        }
    }
}

impl proto::Op {
    pub(crate) fn new(op: &datatypes::Op) -> Self {
        let op = match op {
            datatypes::Op::Uuf(uuf) => proto::op::Op::Uuf(proto::Uuf::new(uuf)),
            datatypes::Op::ZeroExtend(bv_width) => proto::op::Op::ZeroExtend(*bv_width as u32),
            datatypes::Op::RecordGet(attr) => proto::op::Op::RecordGet(attr.to_string()),
            datatypes::Op::StringLike(pattern) => {
                proto::op::Op::StringLike(proto::Pattern::new(pattern))
            }
            datatypes::Op::Ext(ext_op) => proto::op::Op::ExtOp(proto::ExtOp::new(ext_op).into()),
            _ => proto::op::Op::BaseOp(proto::op::BaseOp::new(op).into()),
        };
        Self { op: Some(op) }
    }
}

impl proto::op::BaseOp {
    pub(crate) fn new(op: &datatypes::Op) -> Self {
        #[allow(
            clippy::unreachable,
            reason = "This function is only used within proto::Op::new which ensure unreachable variants are already handled"
        )]
        match op {
            datatypes::Op::Not => proto::op::BaseOp::Not,
            datatypes::Op::And => proto::op::BaseOp::And,
            datatypes::Op::Or => proto::op::BaseOp::Or,
            datatypes::Op::Eq => proto::op::BaseOp::Eq,
            datatypes::Op::Ite => proto::op::BaseOp::Ite,
            datatypes::Op::Bvneg => proto::op::BaseOp::Bvneg,
            datatypes::Op::Bvadd => proto::op::BaseOp::Bvadd,
            datatypes::Op::Bvsub => proto::op::BaseOp::Bvsub,
            datatypes::Op::Bvmul => proto::op::BaseOp::Bvmul,
            datatypes::Op::Bvsdiv => proto::op::BaseOp::Bvsdiv,
            datatypes::Op::Bvudiv => proto::op::BaseOp::Bvudiv,
            datatypes::Op::Bvsrem => proto::op::BaseOp::Bvsrem,
            datatypes::Op::Bvsmod => proto::op::BaseOp::Bvsmod,
            datatypes::Op::Bvurem => proto::op::BaseOp::Bvurem,
            datatypes::Op::Bvshl => proto::op::BaseOp::Bvshl,
            datatypes::Op::Bvlshr => proto::op::BaseOp::Bvlshr,
            datatypes::Op::Bvslt => proto::op::BaseOp::Bvslt,
            datatypes::Op::Bvsle => proto::op::BaseOp::Bvsle,
            datatypes::Op::Bvult => proto::op::BaseOp::Bvult,
            datatypes::Op::Bvule => proto::op::BaseOp::Bvule,
            datatypes::Op::Bvnego => proto::op::BaseOp::Bvnego,
            datatypes::Op::Bvsaddo => proto::op::BaseOp::Bvsaddo,
            datatypes::Op::Bvssubo => proto::op::BaseOp::Bvssubo,
            datatypes::Op::Bvsmulo => proto::op::BaseOp::Bvsmulo,
            datatypes::Op::SetMember => proto::op::BaseOp::SetMember,
            datatypes::Op::SetSubset => proto::op::BaseOp::SetSubset,
            datatypes::Op::SetInter => proto::op::BaseOp::SetInter,
            datatypes::Op::OptionGet => proto::op::BaseOp::OptionGet,
            _ => unreachable!("Other variants should be handled directly by proto::Op::new"),
        }
    }
}

impl proto::Bitvec {
    pub(crate) fn new(bv: &datatypes::Bitvec) -> Self {
        Self {
            width: bv.width as u32,
            val: bv.val.clone(),
        }
    }
}

impl proto::Decimal {
    pub(crate) fn new(dec: &datatypes::Decimal) -> Self {
        Self { d: dec.0 }
    }
}

impl proto::IpAddr {
    pub(crate) fn new(ip: &datatypes::IpAddr) -> Self {
        let cidr = match ip {
            datatypes::IpAddr::V4(cidr) => {
                proto::ip_addr::Version::V4(proto::ip_addr::Cidr::new(cidr))
            }
            datatypes::IpAddr::V6(cidr) => {
                proto::ip_addr::Version::V6(proto::ip_addr::Cidr::new(cidr))
            }
        };
        Self {
            version: Some(cidr),
        }
    }
}

impl proto::ip_addr::Cidr {
    pub(crate) fn new(cidr: &datatypes::Cidr) -> Self {
        Self {
            addr: Some(proto::Bitvec::new(&cidr.addr)),
            pre: cidr.prefix.as_ref().map(proto::Bitvec::new),
        }
    }
}

impl proto::Datetime {
    pub(crate) fn new(dt: &datatypes::Datetime) -> Self {
        Self { val: dt.val }
    }
}

impl proto::Duration {
    pub(crate) fn new(dur: &datatypes::Duration) -> Self {
        Self { val: dur.val }
    }
}

impl proto::ExtType {
    pub(crate) fn new(xty: &datatypes::ExtType) -> Self {
        match xty {
            datatypes::ExtType::IpAddr => proto::ExtType::IpAddrType,
            datatypes::ExtType::Decimal => proto::ExtType::DecimalType,
            datatypes::ExtType::Datetime => proto::ExtType::DatetimeType,
            datatypes::ExtType::Duration => proto::ExtType::DurationType,
        }
    }
}

impl proto::TermPrimType {
    pub(crate) fn new(pty: &datatypes::TermPrimType) -> Self {
        let prim_type = match pty {
            datatypes::TermPrimType::Bitvec { n } => {
                proto::term_prim_type::PrimType::Bitvec(n.get() as u32)
            }
            datatypes::TermPrimType::Entity { ety } => proto::term_prim_type::PrimType::Entity(
                cedar_policy::proto::models::Name::from(ety),
            ),
            datatypes::TermPrimType::Ext { xty } => {
                proto::term_prim_type::PrimType::Ext(proto::ExtType::new(xty).into())
            }
            _ => {
                proto::term_prim_type::PrimType::Prim(proto::term_prim_type::Prim::new(pty).into())
            }
        };
        Self {
            prim_type: Some(prim_type),
        }
    }
}

impl proto::term_prim_type::Prim {
    pub(crate) fn new(pty: &datatypes::TermPrimType) -> Self {
        match pty {
            datatypes::TermPrimType::Bool => Self::Bool,
            datatypes::TermPrimType::String => Self::String,
            _ => unreachable!(
                "Other variants should be handled directly by proto::TermPrimType::new"
            ),
        }
    }
}

impl proto::TermType {
    pub(crate) fn new(ty: &datatypes::TermType) -> Self {
        let term_type = match ty {
            datatypes::TermType::Prim { pty } => {
                proto::term_type::TermType::Prim(proto::TermPrimType::new(pty))
            }
            datatypes::TermType::Option { ty } => {
                proto::term_type::TermType::Option(proto::TermType::new(ty).into())
            }
            datatypes::TermType::Set { ty } => {
                proto::term_type::TermType::Set(proto::TermType::new(ty).into())
            }
            datatypes::TermType::Record { rty } => {
                proto::term_type::TermType::Record(proto::term_type::RecordType::new(rty))
            }
        };
        Self {
            term_type: Some(term_type),
        }
    }
}

impl proto::term_type::RecordField {
    pub(crate) fn new(attr: &str, ty: &datatypes::TermType) -> Self {
        let ty = proto::TermType::new(ty);
        Self {
            attr: attr.to_string(),
            ty: Some(ty),
        }
    }
}

impl proto::term_type::RecordType {
    pub(crate) fn new(fields: &[(SmolStr, datatypes::TermType)]) -> Self {
        Self {
            fields: fields
                .iter()
                .map(|(attr, ty)| proto::term_type::RecordField::new(attr, ty))
                .collect(),
        }
    }
}

impl proto::TermVar {
    pub(crate) fn new(var: &datatypes::TermVar) -> Self {
        Self {
            id: var.id.to_string(),
            ty: Some(proto::TermType::new(&var.ty)),
        }
    }
}

impl proto::Ext {
    pub(crate) fn new(ext: &datatypes::Ext) -> Self {
        let ext = match ext {
            datatypes::Ext::Decimal { d } => proto::ext::Ext::Decimal(proto::Decimal::new(d)),
            datatypes::Ext::Ipaddr { ip } => proto::ext::Ext::Ipaddr(proto::IpAddr::new(ip)),
            datatypes::Ext::Datetime { dt } => proto::ext::Ext::Datetime(proto::Datetime::new(dt)),
            datatypes::Ext::Duration { dur } => {
                proto::ext::Ext::Duration(proto::Duration::new(dur))
            }
        };
        Self { ext: Some(ext) }
    }
}

impl proto::TermPrim {
    pub(crate) fn new(prim: &datatypes::TermPrim) -> Self {
        let prim = match prim {
            datatypes::TermPrim::Bool(b) => proto::term_prim::Prim::Bool(*b),
            datatypes::TermPrim::Bitvec(bv) => {
                proto::term_prim::Prim::Bitvec(proto::Bitvec::new(bv))
            }
            datatypes::TermPrim::String(s) => proto::term_prim::Prim::String(s.to_string()),
            datatypes::TermPrim::Entity(euid) => {
                proto::term_prim::Prim::Entity(cedar_policy::proto::models::EntityUid::from(
                    &cedar_policy::EntityUid::from(euid.clone()),
                ))
            }
            datatypes::TermPrim::Ext(ext) => proto::term_prim::Prim::Ext(proto::Ext::new(ext)),
        };
        Self { prim: Some(prim) }
    }
}

impl proto::Term {
    pub(crate) fn new(term: &datatypes::Term) -> Self {
        let term = match term {
            datatypes::Term::Prim(prim) => proto::term::Term::Prim(proto::TermPrim::new(prim)),
            datatypes::Term::Var(v) => proto::term::Term::Var(proto::TermVar::new(v)),
            datatypes::Term::None(ty) => proto::term::Term::None(proto::TermType::new(ty)),
            datatypes::Term::Some(t) => {
                proto::term::Term::Some(Box::new(proto::Term::new(t.as_ref())))
            }
            datatypes::Term::Set { elts, elts_ty } => {
                proto::term::Term::Set(proto::term::Set::new(elts, elts_ty))
            }
            datatypes::Term::Record(fields) => {
                proto::term::Term::Record(proto::term::Record::new(fields))
            }
            datatypes::Term::App { op, args, ret_ty } => {
                proto::term::Term::App(proto::term::App::new(op, args, ret_ty))
            }
        };
        Self { term: Some(term) }
    }
}

impl proto::term::Set {
    pub(crate) fn new(elts: &[datatypes::Term], elt_ty: &datatypes::TermType) -> Self {
        Self {
            elts: elts.iter().map(proto::Term::new).collect(),
            elt_ty: Some(proto::TermType::new(elt_ty)),
        }
    }
}

impl proto::term::RecordField {
    pub(crate) fn new(attr: &str, value: &datatypes::Term) -> Self {
        Self {
            attr: attr.to_string(),
            term: Some(proto::Term::new(value)),
        }
    }
}

impl proto::term::Record {
    pub(crate) fn new(fields: &[(SmolStr, datatypes::Term)]) -> Self {
        Self {
            fields: fields
                .iter()
                .map(|(attr, value)| proto::term::RecordField::new(attr, value))
                .collect(),
        }
    }
}

impl proto::term::App {
    pub(crate) fn new(
        op: &datatypes::Op,
        args: &[datatypes::Term],
        ret_ty: &datatypes::TermType,
    ) -> Self {
        Self {
            op: Some(proto::Op::new(op)),
            args: args.iter().map(proto::Term::new).collect(),
            ret_ty: Some(proto::TermType::new(ret_ty)),
        }
    }
}

impl proto::Asserts {
    pub(crate) fn new(asserts: &[datatypes::Term]) -> Self {
        Self {
            asserts: asserts.iter().map(proto::Term::new).collect(),
        }
    }
}

impl proto::CheckAssertsRequest {
    pub(crate) fn new(asserts: &[datatypes::Term], request: &RequestEnv) -> Self {
        Self {
            asserts: Some(proto::Asserts::new(asserts)),
            request: Some(proto::RequestEnv::from(request)),
        }
    }
}

impl proto::BatchedAuthorizationRequest {
    pub(crate) fn new(
        policies: &PolicySet,
        schema: &Schema,
        request: &Request,
        entities: &Entities,
        iteration: u32,
    ) -> Self {
        Self {
            policies: Some(cedar_policy::proto::models::PolicySet::from(policies)),
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            request: Some(cedar_policy::proto::models::Request::from(request)),
            entities: Some(cedar_policy::proto::models::Entities::from(entities)),
            iteration,
        }
    }
}

#[cfg(test)]
mod test {
    use cedar_policy::{Context, EntityTypeName, EntityUid, Policy, PolicySet, Schema};

    use prost::Message;
    use std::collections::HashSet;
    use std::str::FromStr;

    use super::*;

    fn example_schema() -> Schema {
        Schema::from_cedarschema_str(
            r#"
            entity Account;
            entity User {
                account: Account
            };
            entity Thing, Box in [Box, Account] {
                owner: User,
                description: String,
                private: Bool
            };
            action view appliesTo {
            principal: [User],
            resource: [Thing, Box],
            context: {
                n1: String
            }
            };
        "#,
        )
        .expect("Example schema failed to parse")
        .0
    }

    #[test]
    fn convert_proto_policy() {
        let policy = Policy::from_str("permit(principal, action, resource);")
            .expect("Failed to parse policy");

        let policy_bytes = proto::Policy::from(&policy).encode_to_vec();
        let policy_proto =
            proto::Policy::decode(&policy_bytes[..]).expect("Failed to decode protobuf policy");

        let policyset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse PolicySet");

        // Serializing a policy is ame as serializing a singleton policyset
        let policyset_proto = cedar_policy::proto::models::PolicySet::from(&policyset);
        let pset_templates = policyset_proto.templates;
        let pset_links = policyset_proto.links;

        let policy_template = policy_proto.template.unwrap();
        let policy_link = policy_proto.policy.unwrap();

        assert_eq!(pset_links, vec![policy_link]);
        assert_eq!(pset_templates, vec![policy_template]);
    }

    #[test]
    fn convert_proto_request_env() {
        let principal_type =
            EntityTypeName::from_str("PrincipalType").expect("Failed to construct PrincipalType");
        let action_name =
            EntityUid::from_str("Action::\"View\"").expect("Failed to construct action name");
        let resource_type =
            EntityTypeName::from_str("ResourceType").expect("Failed to construct ResourceType");
        let request_env = RequestEnv::new(
            principal_type.clone(),
            action_name.clone(),
            resource_type.clone(),
        );

        let request_byes = proto::RequestEnv::from(&request_env).encode_to_vec();
        let request_proto = proto::RequestEnv::decode(&request_byes[..])
            .expect("Failed to decode protobuf RequestEnv");

        let proto_principal = request_proto.principal.unwrap();
        let proto_action = request_proto.action.unwrap();
        let proto_resource = request_proto.resource.unwrap();

        assert_eq!(proto_principal.path.len(), 0);
        assert_eq!(proto_principal.id, principal_type.basename());

        assert_eq!(proto_action.ty.unwrap().id, "Action");
        assert_eq!(proto_action.eid, action_name.id().escaped());

        assert_eq!(proto_resource.path.len(), 0);
        assert_eq!(proto_resource.id, resource_type.basename());
    }

    #[test]
    fn convert_proto_check_policy_request() {
        let policy = Policy::from_str("permit(principal, action, resource);")
            .expect("Failed to parse policy");
        let principal_type =
            EntityTypeName::from_str("User").expect("Failed to construct PrincipalType");
        let action_name =
            EntityUid::from_str("Action::\"View\"").expect("Failed to construct action name");
        let resource_type =
            EntityTypeName::from_str("Box").expect("Failed to construct ResourceType");
        let request_env = RequestEnv::new(
            principal_type.clone(),
            action_name.clone(),
            resource_type.clone(),
        );

        let check_policy_pre_proto = proto::CheckPolicyRequest::new(&policy, &request_env);
        let check_policy_bytes = check_policy_pre_proto.encode_to_vec();
        let check_policy_proto = proto::CheckPolicyRequest::decode(&check_policy_bytes[..])
            .expect("Failed to decode protobuf CheckPolicyReuqest");
        assert_eq!(check_policy_pre_proto, check_policy_proto);

        let policy_proto = check_policy_proto.policy.unwrap();
        let request_proto = check_policy_proto.request.unwrap();

        assert_eq!(
            policy_proto.template.unwrap().id,
            policy.as_ref().template().id().as_ref()
        );

        let proto_principal = request_proto.principal.unwrap();
        let proto_action = request_proto.action.unwrap();
        let proto_resource = request_proto.resource.unwrap();

        assert_eq!(proto_principal.path.len(), 0);
        assert_eq!(proto_principal.id, principal_type.basename());

        assert_eq!(proto_action.ty.unwrap().id, "Action");
        assert_eq!(proto_action.eid, action_name.id().escaped());

        assert_eq!(proto_resource.path.len(), 0);
        assert_eq!(proto_resource.id, resource_type.basename());
    }

    #[test]
    fn convert_proto_check_policyset_request() {
        let policyset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse PolicySet");
        let principal_type =
            EntityTypeName::from_str("User").expect("Failed to construct PrincipalType");
        let action_name =
            EntityUid::from_str("Action::\"View\"").expect("Failed to construct action name");
        let resource_type =
            EntityTypeName::from_str("Box").expect("Failed to construct ResourceType");
        let request_env = RequestEnv::new(
            principal_type.clone(),
            action_name.clone(),
            resource_type.clone(),
        );

        let check_policyset_pre_proto = proto::CheckPolicySetRequest::new(&policyset, &request_env);
        let check_policyset_bytes = check_policyset_pre_proto.encode_to_vec();
        let check_policyset_proto =
            proto::CheckPolicySetRequest::decode(&check_policyset_bytes[..])
                .expect("Failed to decode protobuf CheckPolicyReuqest");
        assert_eq!(check_policyset_pre_proto, check_policyset_proto);

        let policyset_proto = check_policyset_proto.policy_set.unwrap();
        let rt_policyset =
            PolicySet::try_from(policyset_proto).expect("Failed to roundtrip policy");
        let request_proto = check_policyset_proto.request.unwrap();

        assert_eq!(policyset, rt_policyset);

        let proto_principal = request_proto.principal.unwrap();
        let proto_action = request_proto.action.unwrap();
        let proto_resource = request_proto.resource.unwrap();

        assert_eq!(proto_principal.path.len(), 0);
        assert_eq!(proto_principal.id, principal_type.basename());

        assert_eq!(proto_action.ty.unwrap().id, "Action");
        assert_eq!(proto_action.eid, action_name.id().escaped());

        assert_eq!(proto_resource.path.len(), 0);
        assert_eq!(proto_resource.id, resource_type.basename());
    }

    #[test]
    fn convert_proto_compare_policysets_request() {
        let src_policyset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse PolicySet");
        let tgt_policyset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse PolicySet");
        let principal_type =
            EntityTypeName::from_str("User").expect("Failed to construct PrincipalType");
        let action_name =
            EntityUid::from_str("Action::\"View\"").expect("Failed to construct action name");
        let resource_type =
            EntityTypeName::from_str("Thing").expect("Failed to construct ResourceType");
        let request_env = RequestEnv::new(
            principal_type.clone(),
            action_name.clone(),
            resource_type.clone(),
        );

        let compare_policyset_pre_proto =
            proto::ComparePolicySetsRequest::new(&src_policyset, &tgt_policyset, &request_env);
        let compare_policyset_bytes = compare_policyset_pre_proto.encode_to_vec();
        let compare_policyset_proto =
            proto::ComparePolicySetsRequest::decode(&compare_policyset_bytes[..])
                .expect("Failed to decode protobuf CheckPolicyReuqest");
        assert_eq!(compare_policyset_pre_proto, compare_policyset_proto);

        let src_policyset_proto = compare_policyset_proto.src_policy_set.unwrap();
        let rt_src_policyset =
            PolicySet::try_from(src_policyset_proto).expect("Failed to roundtrip policy");
        let tgt_policyset_proto = compare_policyset_proto.tgt_policy_set.unwrap();
        let rt_tgt_policyset =
            PolicySet::try_from(tgt_policyset_proto).expect("Failed to roundtrip policy");
        let request_proto = compare_policyset_proto.request.unwrap();

        assert_eq!(src_policyset, rt_src_policyset);
        assert_eq!(tgt_policyset, rt_tgt_policyset);
        let proto_principal = request_proto.principal.unwrap();
        let proto_action = request_proto.action.unwrap();
        let proto_resource = request_proto.resource.unwrap();

        assert_eq!(proto_principal.path.len(), 0);
        assert_eq!(proto_principal.id, principal_type.basename());

        assert_eq!(proto_action.ty.unwrap().id, "Action");
        assert_eq!(proto_action.eid, action_name.id().escaped());

        assert_eq!(proto_resource.path.len(), 0);
        assert_eq!(proto_resource.id, resource_type.basename());
    }

    #[test]
    fn convert_proto_authorization_request() {
        let policyset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse PolicySet");

        let principal = EntityUid::from_str("User::\"Alice\"").expect("Failed to parse principal");
        let action = EntityUid::from_str("Action::\"View\"").expect("Failed to parse action");
        let resource = EntityUid::from_str("Box::\"Nice Box\"").expect("Failed to parse resource");
        let context = Context::empty();
        let request = Request::new(principal, action, resource, context, None)
            .expect("Failed to construct Request");
        let entities = Entities::empty();

        let authorization_pre_proto =
            proto::AuthorizationRequest::new(&policyset, &entities, &request);
        let authorization_bytes = authorization_pre_proto.encode_to_vec();
        let authorization_proto = proto::AuthorizationRequest::decode(&authorization_bytes[..])
            .expect("Failed to decode protobuf Authorization Request");
        assert_eq!(authorization_pre_proto, authorization_proto);

        let rt_policyset = PolicySet::try_from(authorization_proto.policies.unwrap())
            .expect("Failed to round-trip policies");
        let rt_entities = Entities::try_from(authorization_proto.entities.unwrap()).unwrap();
        let rt_request = Request::try_from(authorization_proto.request.unwrap()).unwrap();

        assert_eq!(policyset, rt_policyset);
        assert_eq!(entities, rt_entities);
        assert_eq!(request.principal(), rt_request.principal());
        assert_eq!(request.action(), rt_request.action());
        assert_eq!(request.resource(), rt_request.resource());
    }

    #[test]
    fn convert_proto_evaluation_request_checked() {
        let expr = cedar_policy::Expression::from_str("0 + 1").expect("Failed to parse expression");
        let expected =
            cedar_policy::Expression::from_str("1").expect("Failed to parse expected output");

        let principal = EntityUid::from_str("User::\"Alice\"").expect("Failed to parse principal");
        let action = EntityUid::from_str("Action::\"View\"").expect("Failed to parse action");
        let resource = EntityUid::from_str("Box::\"Nice Box\"").expect("Failed to parse resource");
        let context = Context::empty();
        let request = Request::new(principal, action, resource, context, None)
            .expect("Failed to construct Request");
        let entities = Entities::empty();

        let eval_unchecked_pre_proto =
            proto::EvaluationRequestChecked::new(&expr, &entities, &request);
        let eval_unchecked_bytes = eval_unchecked_pre_proto.encode_to_vec();
        let eval_unchecked_proto =
            proto::EvaluationRequestChecked::decode(&eval_unchecked_bytes[..])
                .expect("Failed to decode protobuf unchecked Evaluation Request");
        assert_eq!(eval_unchecked_proto, eval_unchecked_pre_proto);

        let eval_checked_pre_proto = proto::EvaluationRequestChecked::new_checked(
            &expr,
            &entities,
            &request,
            Some(&expected),
        );
        let eval_checked_bytes = eval_checked_pre_proto.encode_to_vec();
        let eval_checked_proto = proto::EvaluationRequestChecked::decode(&eval_checked_bytes[..])
            .expect("Failed to decode protobuf checked Evaluation Request");
        assert_eq!(eval_checked_proto, eval_checked_pre_proto);

        assert_eq!(eval_checked_proto.expr, eval_unchecked_proto.expr);
        assert_eq!(eval_checked_proto.request, eval_unchecked_proto.request);
        assert_eq!(eval_checked_proto.entities, eval_unchecked_proto.entities);
        assert_eq!(eval_unchecked_proto.expected, None);
        eval_checked_proto.expected.unwrap();
    }

    #[test]
    fn convert_proto_validation_request() {
        let policyset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse PolicySet");

        let schema = example_schema();
        let mode = ValidationMode::Strict;

        let validation_request_pre_proto =
            proto::ValidationRequest::new(&policyset, &schema, &mode);
        let validation_request_bytes = validation_request_pre_proto.encode_to_vec();
        let validation_request_proto =
            proto::ValidationRequest::decode(&validation_request_bytes[..])
                .expect("Failed to decode protobuf validation request");
        assert_eq!(validation_request_pre_proto, validation_request_proto);

        let rt_pset = PolicySet::try_from(validation_request_proto.policies.unwrap())
            .expect("Failed to roundtrip PolicySet");
        let rt_schema = Schema::try_from(validation_request_proto.schema.unwrap()).unwrap();

        assert_eq!(policyset, rt_pset);

        // Need to collect into a collection that is either unordered or is first sorted
        assert_eq!(
            rt_schema.principals().collect::<HashSet<_>>(),
            schema.principals().collect::<HashSet<_>>()
        );
        assert_eq!(
            rt_schema.actions().collect::<HashSet<_>>(),
            schema.actions().collect::<HashSet<_>>()
        );
        assert_eq!(
            rt_schema.resources().collect::<HashSet<_>>(),
            schema.resources().collect::<HashSet<_>>()
        );
    }

    #[test]
    fn convert_proto_level_validation_request() {
        let policyset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse PolicySet");

        let schema = example_schema();
        let level = 4;

        let validation_request_pre_proto =
            proto::LevelValidationRequest::new(&policyset, &schema, level);
        let validation_request_bytes = validation_request_pre_proto.encode_to_vec();
        let validation_request_proto =
            proto::LevelValidationRequest::decode(&validation_request_bytes[..])
                .expect("Failed to decode protobuf level validation request");
        assert_eq!(validation_request_pre_proto, validation_request_proto);

        let rt_pset = PolicySet::try_from(validation_request_proto.policies.unwrap())
            .expect("Failed to roundtrip PolicySet");
        let rt_schema = Schema::try_from(validation_request_proto.schema.unwrap()).unwrap();

        assert_eq!(policyset, rt_pset);

        // Need to collect into a collection that is either unordered or is first sorted
        assert_eq!(
            rt_schema.principals().collect::<HashSet<_>>(),
            schema.principals().collect::<HashSet<_>>()
        );
        assert_eq!(
            rt_schema.actions().collect::<HashSet<_>>(),
            schema.actions().collect::<HashSet<_>>()
        );
        assert_eq!(
            rt_schema.resources().collect::<HashSet<_>>(),
            schema.resources().collect::<HashSet<_>>()
        );
        assert_eq!(level, validation_request_proto.level);
    }

    #[test]
    fn convert_entity_validation_request() {
        let schema = example_schema();
        let entities = Entities::empty();

        let validation_request_pre_proto = proto::EntityValidationRequest::new(&schema, &entities);
        let validation_request_bytes = validation_request_pre_proto.encode_to_vec();
        let validation_request_proto =
            proto::EntityValidationRequest::decode(&validation_request_bytes[..])
                .expect("Failed to decode protobuf entity validation request");
        assert_eq!(validation_request_pre_proto, validation_request_proto);

        let rt_schema = Schema::try_from(validation_request_proto.schema.unwrap()).unwrap();
        let rt_entities = Entities::try_from(validation_request_proto.entities.unwrap()).unwrap();

        // Need to collect into a collection that is either unordered or is first sorted
        assert_eq!(
            rt_schema.principals().collect::<HashSet<_>>(),
            schema.principals().collect::<HashSet<_>>()
        );
        assert_eq!(
            rt_schema.actions().collect::<HashSet<_>>(),
            schema.actions().collect::<HashSet<_>>()
        );
        assert_eq!(
            rt_schema.resources().collect::<HashSet<_>>(),
            schema.resources().collect::<HashSet<_>>()
        );
        assert_eq!(entities, rt_entities);
    }

    #[test]
    fn convert_proto_request_validation_request() {
        let schema = example_schema();
        let principal = EntityUid::from_str("User::\"Alice\"").expect("Failed to parse principal");
        let action = EntityUid::from_str("Action::\"View\"").expect("Failed to parse action");
        let resource = EntityUid::from_str("Box::\"Nice Box\"").expect("Failed to parse resource");
        let context = Context::empty();
        let request = Request::new(principal, action, resource, context, None)
            .expect("Failed to construct Request");

        let validation_request_pre_proto = proto::RequestValidationRequest::new(&schema, &request);
        let validation_request_bytes = validation_request_pre_proto.encode_to_vec();
        let validation_request_proto =
            proto::RequestValidationRequest::decode(&validation_request_bytes[..])
                .expect("Failed to decode protobuf request validation request");
        assert_eq!(validation_request_pre_proto, validation_request_proto);

        let rt_schema = Schema::try_from(validation_request_proto.schema.unwrap()).unwrap();
        let rt_request = Request::try_from(validation_request_proto.request.unwrap()).unwrap();

        // Need to collect into a collection that is either unordered or is first sorted
        assert_eq!(
            rt_schema.principals().collect::<HashSet<_>>(),
            schema.principals().collect::<HashSet<_>>()
        );
        assert_eq!(
            rt_schema.actions().collect::<HashSet<_>>(),
            schema.actions().collect::<HashSet<_>>()
        );
        assert_eq!(
            rt_schema.resources().collect::<HashSet<_>>(),
            schema.resources().collect::<HashSet<_>>()
        );

        assert_eq!(request.principal(), rt_request.principal());
        assert_eq!(request.action(), rt_request.action());
        assert_eq!(request.resource(), rt_request.resource());
    }
}
