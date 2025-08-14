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
    pub(crate) schema: Schema,
    pub(crate) request: RequestEnv,
}

impl proto::CheckPolicyRequest {
    pub(crate) fn new(policy: &Policy, schema: &Schema, request: &RequestEnv) -> Self {
        Self {
            policy: Some(proto::Policy::from(policy)),
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            request: Some(proto::RequestEnv::from(request)),
        }
    }
}

/// Serialize the symcc request arguments to a ProtoBuf message
impl From<&CheckPolicyRequest> for proto::CheckPolicyRequest {
    fn from(req: &CheckPolicyRequest) -> Self {
        Self::new(&req.policy, &req.schema, &req.request)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CheckPolicySetRequest {
    pub(crate) policyset: PolicySet,
    pub(crate) schema: Schema,
    pub(crate) request: RequestEnv,
}

impl proto::CheckPolicySetRequest {
    pub(crate) fn new(policyset: &PolicySet, schema: &Schema, request: &RequestEnv) -> Self {
        Self {
            policy_set: Some(cedar_policy::proto::models::PolicySet::from(policyset)),
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            request: Some(proto::RequestEnv::from(request)),
        }
    }
}

/// Serialize the symcc request arguments to a ProtoBuf message
impl From<&CheckPolicySetRequest> for proto::CheckPolicySetRequest {
    fn from(req: &CheckPolicySetRequest) -> Self {
        Self::new(&req.policyset, &req.schema, &req.request)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ComparePolicySetsRequest {
    pub(crate) src_policyset: PolicySet,
    pub(crate) tgt_policyset: PolicySet,
    pub(crate) schema: Schema,
    pub(crate) request: RequestEnv,
}

impl proto::ComparePolicySetsRequest {
    pub(crate) fn new(
        src_policyset: &PolicySet,
        tgt_policyset: &PolicySet,
        schema: &Schema,
        request: &RequestEnv,
    ) -> Self {
        Self {
            src_policy_set: Some(cedar_policy::proto::models::PolicySet::from(src_policyset)),
            tgt_policy_set: Some(cedar_policy::proto::models::PolicySet::from(tgt_policyset)),
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            request: Some(proto::RequestEnv::from(request)),
        }
    }
}

/// Serialize the symcc request arguments to a ProtoBuf message
impl From<&ComparePolicySetsRequest> for proto::ComparePolicySetsRequest {
    fn from(req: &ComparePolicySetsRequest) -> Self {
        Self::new(
            &req.src_policyset,
            &req.tgt_policyset,
            &req.schema,
            &req.request,
        )
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

impl proto::Uuf {
    pub(crate) fn new(uuf: &datatypes::Uuf) -> Self {
        Self {
            id: uuf.id.clone(),
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
    pub(crate) fn new(pattern: &Vec<datatypes::PatElem>) -> Self {
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
            datatypes::Op::RecordGet(attr) => proto::op::Op::RecordGet(attr.clone()),
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
            datatypes::Op::Bvumod => proto::op::BaseOp::Bvumod,
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
                proto::term_prim_type::PrimType::Bitvec(*n as u32)
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
                proto::term_type::TermType::Prim(proto::TermPrimType::new(pty).into())
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
    pub(crate) fn new(fields: &Vec<(String, datatypes::TermType)>) -> Self {
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
            id: var.id.clone(),
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
            datatypes::TermPrim::String(s) => proto::term_prim::Prim::String(s.clone()),
            datatypes::TermPrim::Entity(euid) => {
                proto::term_prim::Prim::Entity(cedar_policy::proto::models::EntityUid::from(euid))
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
    pub(crate) fn new(elts: &Vec<datatypes::Term>, elt_ty: &datatypes::TermType) -> Self {
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
    pub(crate) fn new(fields: &Vec<(String, datatypes::Term)>) -> Self {
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
        args: &Vec<datatypes::Term>,
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
    pub(crate) fn new(asserts: &Vec<datatypes::Term>) -> Self {
        Self {
            asserts: asserts.iter().map(proto::Term::new).collect(),
        }
    }
}

impl proto::CheckAssertsRequest {
    pub(crate) fn new(
        asserts: &Vec<datatypes::Term>,
        schema: &Schema,
        request: &RequestEnv,
    ) -> Self {
        Self {
            asserts: Some(proto::Asserts::new(asserts)),
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            request: Some(proto::RequestEnv::from(request)),
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
        let schema = example_schema();
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

        let check_policy_pre_proto = proto::CheckPolicyRequest::new(&policy, &schema, &request_env);
        let check_policy_bytes = check_policy_pre_proto.encode_to_vec();
        let check_policy_proto = proto::CheckPolicyRequest::decode(&check_policy_bytes[..])
            .expect("Failed to decode protobuf CheckPolicyReuqest");
        assert_eq!(check_policy_pre_proto, check_policy_proto);

        let policy_proto = check_policy_proto.policy.unwrap();
        let rt_schema = cedar_policy::Schema::from(&check_policy_proto.schema.unwrap());
        let request_proto = check_policy_proto.request.unwrap();

        assert_eq!(
            policy_proto.template.unwrap().id,
            policy.as_ref().template().id().as_ref()
        );
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
        let schema = example_schema();
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

        let check_policyset_pre_proto =
            proto::CheckPolicySetRequest::new(&policyset, &schema, &request_env);
        let check_policyset_bytes = check_policyset_pre_proto.encode_to_vec();
        let check_policyset_proto =
            proto::CheckPolicySetRequest::decode(&check_policyset_bytes[..])
                .expect("Failed to decode protobuf CheckPolicyReuqest");
        assert_eq!(check_policyset_pre_proto, check_policyset_proto);

        let policyset_proto = check_policyset_proto.policy_set.unwrap();
        let rt_policyset =
            PolicySet::try_from(&policyset_proto).expect("Failed to roundtrip policy");
        let rt_schema = Schema::from(&check_policyset_proto.schema.unwrap());
        let request_proto = check_policyset_proto.request.unwrap();

        assert_eq!(policyset, rt_policyset);
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
        let schema = example_schema();
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

        let compare_policyset_pre_proto = proto::ComparePolicySetsRequest::new(
            &src_policyset,
            &tgt_policyset,
            &schema,
            &request_env,
        );
        let compare_policyset_bytes = compare_policyset_pre_proto.encode_to_vec();
        let compare_policyset_proto =
            proto::ComparePolicySetsRequest::decode(&compare_policyset_bytes[..])
                .expect("Failed to decode protobuf CheckPolicyReuqest");
        assert_eq!(compare_policyset_pre_proto, compare_policyset_proto);

        let src_policyset_proto = compare_policyset_proto.src_policy_set.unwrap();
        let rt_src_policyset =
            PolicySet::try_from(&src_policyset_proto).expect("Failed to roundtrip policy");
        let tgt_policyset_proto = compare_policyset_proto.tgt_policy_set.unwrap();
        let rt_tgt_policyset =
            PolicySet::try_from(&tgt_policyset_proto).expect("Failed to roundtrip policy");
        let rt_schema = Schema::from(&compare_policyset_proto.schema.unwrap());
        let request_proto = compare_policyset_proto.request.unwrap();

        assert_eq!(src_policyset, rt_src_policyset);
        assert_eq!(tgt_policyset, rt_tgt_policyset);
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

        let rt_policyset = PolicySet::try_from(&authorization_proto.policies.unwrap())
            .expect("Failed to round-trip policies");
        let rt_entities = Entities::from(&authorization_proto.entities.unwrap());
        let rt_request = Request::from(&authorization_proto.request.unwrap());

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

        let rt_pset = PolicySet::try_from(&validation_request_proto.policies.unwrap())
            .expect("Failed to roundtrip PolicySet");
        let rt_schema = Schema::from(&validation_request_proto.schema.unwrap());

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

        let rt_pset = PolicySet::try_from(&validation_request_proto.policies.unwrap())
            .expect("Failed to roundtrip PolicySet");
        let rt_schema = Schema::from(&validation_request_proto.schema.unwrap());

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

        let rt_schema = Schema::from(&validation_request_proto.schema.unwrap());
        let rt_entities = Entities::from(&validation_request_proto.entities.unwrap());

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

        let rt_schema = Schema::from(&validation_request_proto.schema.unwrap());
        let rt_request = Request::from(&validation_request_proto.request.unwrap());

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
