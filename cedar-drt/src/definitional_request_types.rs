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

pub use cedar_policy_core::*;
pub use cedar_policy_validator::{ValidationMode, ValidatorSchema};
use cedar_testing::cedar_test_impl::ExprOrValue;
pub use entities::Entities;
use serde::{Deserialize, Serialize};

pub mod proto {
    #![allow(missing_docs)]
    include!(concat!(env!("OUT_DIR"), "/cedar_drt.rs"));
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AuthorizationRequestMsg {
    pub request: ast::Request,
    pub policies: ast::PolicySet,
    pub entities: Entities,
}

impl From<&proto::AuthorizationRequestMsg> for AuthorizationRequestMsg {
    fn from(v: &proto::AuthorizationRequestMsg) -> Self {
        let request = ast::Request::from(v.request.as_ref().unwrap());

        Self {
            request: request,
            policies: ast::PolicySet::try_from(v.policies.as_ref().unwrap()).expect("Failed to parse policy set"),
            entities: Entities::from(v.entities.as_ref().unwrap())
        }
    }
}

impl From<&AuthorizationRequestMsg> for proto::AuthorizationRequestMsg {
    fn from(v: &AuthorizationRequestMsg) -> Self {
        Self {
            request: Some(ast::proto::Request::from(&v.request)),
            policies: Some(ast::proto::LiteralPolicySet::from(&v.policies)),
            entities: Some(ast::proto::Entities::from(&v.entities))
        }
    }
}

pub struct ValidationRequestMsg {
    pub schema: ValidatorSchema,
    pub policies: ast::PolicySet,
    pub mode: ValidationMode,
}

impl From<&proto::ValidationRequestMsg> for ValidationRequestMsg {
    fn from(v: &proto::ValidationRequestMsg) -> Self {
        Self {
            schema: ValidatorSchema::from(v.schema.as_ref().unwrap()),
            policies: ast::PolicySet::try_from(v.policies.as_ref().unwrap()).expect("Failed to parse policy set"),
            mode: ValidationMode::from(&cedar_policy_validator::proto::ValidationMode::try_from(v.mode).unwrap())
        }
    }
}

impl From<&ValidationRequestMsg> for proto::ValidationRequestMsg {
    fn from(v: &ValidationRequestMsg) -> Self {
        Self {
            schema: Some(cedar_policy_validator::proto::ValidatorSchema::from(&v.schema)),
            policies: Some(ast::proto::LiteralPolicySet::from(&v.policies)),
            mode: cedar_policy_validator::proto::ValidationMode::from(&v.mode).into()
        }
    }
}


#[derive(Debug, Serialize)]
pub struct AuthorizationRequest<'a> {
    pub request: &'a ast::Request,
    pub policies: &'a ast::PolicySet,
    pub entities: &'a Entities,
}

#[derive(Debug, Serialize)]
pub struct EvaluationRequest<'a> {
    pub request: &'a ast::Request,
    pub entities: &'a Entities,
    pub expr: &'a ast::Expr,
    pub expected: Option<&'a ast::Expr>,
}

#[derive(Debug, Serialize)]
pub struct PartialEvaluationRequest<'a> {
    pub request: &'a ast::Request,
    pub entities: &'a Entities,
    pub expr: &'a ast::Expr,
    pub expected: Option<ExprOrValue>,
}

#[derive(Debug, Serialize)]
pub struct PartialAuthorizationRequest<'a> {
    pub request: &'a ast::Request,
    pub entities: &'a Entities,
    pub policies: &'a ast::PolicySet,
}

#[derive(Debug, Serialize)]
pub struct ValidationRequest<'a> {
    pub schema: &'a ValidatorSchema,
    pub policies: &'a ast::PolicySet,
    pub mode: ValidationMode,
}

#[derive(Debug, Serialize)]
pub struct RequestValidationRequest<'a> {
    pub schema: &'a ValidatorSchema,
    pub request: &'a ast::Request,
}

#[derive(Debug, Serialize)]
pub struct EntityValidationRequest<'a> {
    pub schema: &'a ValidatorSchema,
    pub entities: &'a Entities,
}
