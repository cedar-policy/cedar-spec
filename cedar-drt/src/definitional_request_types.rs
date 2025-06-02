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

pub use cedar_policy_core::validator::{ValidationMode, ValidatorSchema};
pub use cedar_policy_core::*;
pub use entities::Entities;

pub mod proto {
    #![allow(missing_docs)]
    include!(concat!(env!("OUT_DIR"), "/cedar_drt.rs"));
}

#[derive(Clone, Debug)]
pub struct AuthorizationRequest<'a> {
    pub request: &'a ast::Request,
    pub policies: &'a ast::PolicySet,
    pub entities: &'a Entities,
}

impl From<&AuthorizationRequest<'_>> for proto::AuthorizationRequest {
    fn from(v: &AuthorizationRequest<'_>) -> Self {
        Self {
            request: Some(cedar_policy::proto::models::Request::from(v.request)),
            policies: Some(cedar_policy::proto::models::PolicySet::from(v.policies)),
            entities: Some(cedar_policy::proto::models::Entities::from(v.entities)),
        }
    }
}

// Converting `AuthorizationRequest` from proto to non-proto structures is
// only required for some roundtrip tests
#[derive(Clone, Debug)]
pub struct OwnedAuthorizationRequest {
    pub request: ast::Request,
    pub policies: ast::PolicySet,
    pub entities: Entities,
}

impl From<proto::AuthorizationRequest> for OwnedAuthorizationRequest {
    fn from(v: proto::AuthorizationRequest) -> Self {
        Self {
            request: ast::Request::from(&v.request.unwrap_or_default()),
            policies: ast::PolicySet::try_from(&v.policies.unwrap_or_default())
                .expect("proto-encoded policy set should be a valid policy set"),
            entities: Entities::from(&v.entities.unwrap_or_default()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ValidationRequest<'a> {
    pub schema: &'a ValidatorSchema,
    pub policies: &'a ast::PolicySet,
    pub mode: ValidationMode,
}

impl From<&ValidationRequest<'_>> for proto::ValidationRequest {
    fn from(v: &ValidationRequest<'_>) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(v.schema)),
            policies: Some(cedar_policy::proto::models::PolicySet::from(v.policies)),
            mode: cedar_policy::proto::models::ValidationMode::from(&v.mode).into(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct LevelValidationRequest<'a> {
    pub schema: &'a ValidatorSchema,
    pub policies: &'a ast::PolicySet,
    pub level: i32,
}

impl From<&LevelValidationRequest<'_>> for proto::LevelValidationRequest {
    fn from(v: &LevelValidationRequest<'_>) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(v.schema)),
            policies: Some(cedar_policy::proto::models::PolicySet::from(v.policies)),
            level: v.level,
        }
    }
}

#[derive(Clone, Debug)]
pub struct EvaluationRequest<'a> {
    pub request: &'a ast::Request,
    pub entities: &'a Entities,
    pub expr: &'a ast::Expr,
    pub expected: Option<&'a ast::Expr>,
}

impl From<&EvaluationRequest<'_>> for proto::EvaluationRequest {
    fn from(v: &EvaluationRequest<'_>) -> Self {
        Self {
            expr: Some(cedar_policy::proto::models::Expr::from(v.expr)),
            request: Some(cedar_policy::proto::models::Request::from(v.request)),
            entities: Some(cedar_policy::proto::models::Entities::from(v.entities)),
            expected: v.expected.map(cedar_policy::proto::models::Expr::from),
        }
    }
}

#[derive(Debug, Clone)]
pub struct RequestValidationRequest<'a> {
    pub schema: &'a ValidatorSchema,
    pub request: &'a ast::Request,
}

impl From<&RequestValidationRequest<'_>> for proto::RequestValidationRequest {
    fn from(v: &RequestValidationRequest<'_>) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(v.schema)),
            request: Some(cedar_policy::proto::models::Request::from(v.request)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct EntityValidationRequest<'a> {
    pub schema: &'a ValidatorSchema,
    pub entities: &'a Entities,
}

impl From<&EntityValidationRequest<'_>> for proto::EntityValidationRequest {
    fn from(v: &EntityValidationRequest<'_>) -> Self {
        Self {
            schema: Some(cedar_policy::proto::models::Schema::from(v.schema)),
            entities: Some(cedar_policy::proto::models::Entities::from(v.entities)),
        }
    }
}
