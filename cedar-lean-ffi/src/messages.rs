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
pub use cedar_policy::{
    Entities, Expression, Policy, PolicySet, Request, RequestEnv, Schema, ValidationMode,
};

pub mod proto {
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
pub struct CheckPolicyRequest {
    pub policy: Policy,
    pub schema: Schema,
    pub request: RequestEnv,
}

impl proto::CheckPolicyRequest {
    pub fn new(policy: &Policy, schema: &Schema, request: &RequestEnv) -> Self {
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
pub struct CheckPolicySetRequest {
    pub policyset: PolicySet,
    pub schema: Schema,
    pub request: RequestEnv,
}

impl proto::CheckPolicySetRequest {
    pub fn new(policyset: &PolicySet, schema: &Schema, request: &RequestEnv) -> Self {
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
pub struct ComparePolicySetsRequest {
    pub src_policyset: PolicySet,
    pub tgt_policyset: PolicySet,
    pub schema: Schema,
    pub request: RequestEnv,
}

impl proto::ComparePolicySetsRequest {
    pub fn new(
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
    pub fn new(policyset: &PolicySet, entities: &Entities, request: &Request) -> Self {
        Self {
            request: Some(cedar_policy::proto::models::Request::from(request)),
            policies: Some(cedar_policy::proto::models::PolicySet::from(policyset)),
            entities: Some(cedar_policy::proto::models::Entities::from(entities)),
        }
    }
}

/// Serialize an Expression evaluation request (checked or unchecked)
impl proto::EvaluationRequestChecked {
    pub fn new(expr: &Expression, entities: &Entities, request: &Request) -> Self {
        Self {
            expr: Some(cedar_policy::proto::models::Expr::from(expr)),
            request: Some(cedar_policy::proto::models::Request::from(request)),
            entities: Some(cedar_policy::proto::models::Entities::from(entities)),
            expected: None,
        }
    }

    pub fn new_checked(
        expr: &Expression,
        entities: &Entities,
        request: &Request,
        expected: &Expression,
    ) -> Self {
        Self {
            expr: Some(cedar_policy::proto::models::Expr::from(expr)),
            request: Some(cedar_policy::proto::models::Request::from(request)),
            entities: Some(cedar_policy::proto::models::Entities::from(entities)),
            expected: Some(cedar_policy::proto::models::Expr::from(expected)),
        }
    }
}

/// Serialize a PolicySet validation request
impl proto::ValidationRequest {
    pub fn new(policyset: &PolicySet, schema: &Schema, mode: &ValidationMode) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            policies: Some(cedar_policy::proto::models::PolicySet::from(policyset)),
            mode: cedar_policy::proto::models::ValidationMode::from(&mode.clone().into()).into(),
        }
    }
}

/// Serialize a PolicySet level-validation request
impl proto::LevelValidationRequest {
    pub fn new(policyset: &PolicySet, schema: &Schema, level: i32) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            policies: Some(cedar_policy::proto::models::PolicySet::from(policyset)),
            level: level,
        }
    }
}

/// Serialize an entities validation request
impl proto::EntityValidationRequest {
    pub fn new(schema: &Schema, entities: &Entities) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            entities: Some(cedar_policy::proto::models::Entities::from(entities)),
        }
    }
}

/// Serialize a request validation request
impl proto::RequestValidationRequest {
    pub fn new(schema: &Schema, request: &Request) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(schema)),
            request: Some(cedar_policy::proto::models::Request::from(request)),
        }
    }
}
