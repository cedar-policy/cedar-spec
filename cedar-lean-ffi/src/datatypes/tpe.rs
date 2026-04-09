/// Lean TPE return types
use cedar_policy::{Decision, EntityTypeName, PolicyId};
use serde::Deserialize;
use serde_with::{TryFromInto, serde_as};
use std::collections::HashSet;

use super::{ExtType, NameDef, PatElem, Value};
use crate::FfiError;

/// TPE Response (partial authorization)
/// Note: Sets are serialized as flat JSON arrays by the Lean TPE's custom ToJson
/// instance (unlike the authorization Response which uses the derived {"mk":{"l":[...]}} format)
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct TpeResponseInner {
    pub(crate) decision: Option<String>,
    #[serde(rename = "satisfiedPermits")]
    pub(crate) satisfied_permits: Vec<String>,
    #[serde(rename = "falsePermits")]
    pub(crate) false_permits: Vec<String>,
    #[serde(rename = "errorPermits")]
    pub(crate) error_permits: Vec<String>,
    #[serde(rename = "residualPermits")]
    pub(crate) residual_permits: Vec<String>,
    #[serde(rename = "satisfiedForbids")]
    pub(crate) satisfied_forbids: Vec<String>,
    #[serde(rename = "falseForbids")]
    pub(crate) false_forbids: Vec<String>,
    #[serde(rename = "errorForbids")]
    pub(crate) error_forbids: Vec<String>,
    #[serde(rename = "residualForbids")]
    pub(crate) residual_forbids: Vec<String>,
    pub(crate) residuals: Vec<ResidualPolicyDef>,
}

/// TPE ResidualPolicy (internal deserialization)
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct ResidualPolicyDef {
    pub(crate) id: String,
    pub(crate) effect: String,
    pub(crate) residual: Residual,
}

/// Lean BoolType: mirrors `Cedar.Validation.BoolType`
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum BoolType {
    AnyBool,
    Tt,
    Ff,
}

/// Lean qualified type: mirrors `Cedar.Validation.Qualified`
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Qualified<T> {
    Optional { a: T },
    Required { a: T },
}

/// Lean CedarType: mirrors `Cedar.Validation.CedarType`
#[serde_as]
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum CedarType {
    Bool {
        bty: BoolType,
    },
    Int,
    String,
    Entity {
        #[serde_as(as = "TryFromInto<NameDef>")]
        ety: EntityTypeName,
    },
    Set {
        ty: Box<CedarType>,
    },
    /// Lean serializes `Map Attr (Qualified CedarType)` as an array of `[key, value]` pairs
    Record {
        rty: Vec<(String, Qualified<CedarType>)>,
    },
    Ext {
        xty: ExtType,
    },
}

/// Lean Var: mirrors `Cedar.Spec.Var`
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Var {
    Principal,
    Action,
    Resource,
    Context,
}

/// Lean UnaryOp: mirrors `Cedar.Spec.UnaryOp`
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum UnaryOp {
    Not,
    Neg,
    IsEmpty,
    Like {
        p: Vec<PatElem>,
    },
    Is {
        #[serde(deserialize_with = "deserialize_entity_type")]
        ety: EntityTypeName,
    },
}

/// Lean BinaryOp: mirrors `Cedar.Spec.BinaryOp`
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum BinaryOp {
    Eq,
    Mem,
    HasTag,
    GetTag,
    Less,
    LessEq,
    Add,
    Sub,
    Mul,
    Contains,
    ContainsAll,
    ContainsAny,
}

/// Lean ExtFun: mirrors `Cedar.Spec.ExtFun`
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ExtFun {
    Decimal,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Ip,
    IsIpv4,
    IsIpv6,
    IsLoopback,
    IsMulticast,
    IsInRange,
    Datetime,
    Duration,
    Offset,
    DurationSince,
    ToDate,
    ToTime,
    ToMilliseconds,
    ToSeconds,
    ToMinutes,
    ToHours,
    ToDays,
}

/// Lean TPE Residual: mirrors `Cedar.TPE.Residual`
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Residual {
    /// val (v : Value) (ty : CedarType)
    Val { v: Value, ty: CedarType },
    /// var (v : Var)  (ty : CedarType)
    Var { v: Var, ty: CedarType },
    /// ite (cond : Residual) (thenExpr : Residual) (elseExpr : Residual)  (ty : CedarType)
    Ite {
        cond: Box<Residual>,
        #[serde(rename = "thenExpr")]
        then_expr: Box<Residual>,
        #[serde(rename = "elseExpr")]
        else_expr: Box<Residual>,
        ty: CedarType,
    },
    /// and (a : Residual) (b : Residual)  (ty : CedarType)
    And {
        a: Box<Residual>,
        b: Box<Residual>,
        ty: CedarType,
    },
    /// or (a : Residual) (b : Residual)  (ty : CedarType)
    Or {
        a: Box<Residual>,
        b: Box<Residual>,
        ty: CedarType,
    },
    /// unaryApp (op : UnaryOp) (expr : Residual)  (ty : CedarType)
    UnaryApp {
        op: UnaryOp,
        expr: Box<Residual>,
        ty: CedarType,
    },
    /// binaryApp (op : BinaryOp) (a : Residual) (b : Residual)  (ty : CedarType)
    BinaryApp {
        op: BinaryOp,
        a: Box<Residual>,
        b: Box<Residual>,
        ty: CedarType,
    },
    /// getAttr (expr : Residual) (attr : Attr)  (ty : CedarType)
    GetAttr {
        expr: Box<Residual>,
        attr: String,
        ty: CedarType,
    },
    /// hasAttr (expr : Residual) (attr : Attr)  (ty : CedarType)
    HasAttr {
        expr: Box<Residual>,
        attr: String,
        ty: CedarType,
    },
    /// set (ls : List Residual)  (ty : CedarType)
    Set { ls: Vec<Residual>, ty: CedarType },
    /// record (map : List (Attr × Residual))  (ty : CedarType)
    Record {
        map: Vec<(String, Residual)>,
        ty: CedarType,
    },
    /// call (xfn : ExtFun) (args : List Residual) (ty : CedarType)
    Call {
        xfn: ExtFun,
        args: Vec<Residual>,
        ty: CedarType,
    },
    /// error (ty : CedarType)
    Error { ty: CedarType },
}

/// Helper to deserialize EntityType (which is just a Name) from Lean's JSON format
fn deserialize_entity_type<'de, D>(deserializer: D) -> Result<EntityTypeName, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let name_def = NameDef::deserialize(deserializer)?;
    EntityTypeName::try_from(name_def).map_err(serde::de::Error::custom)
}

/// Public TPE residual policy
#[derive(Debug)]
pub struct TpeResidualPolicy {
    pub id: PolicyId,
    pub effect: String,
    pub residual: Residual,
}

/// Public TPE response
#[derive(Debug)]
pub struct TpeResponse {
    pub decision: Option<Decision>,
    pub satisfied_permits: HashSet<PolicyId>,
    pub false_permits: HashSet<PolicyId>,
    pub error_permits: HashSet<PolicyId>,
    pub residual_permits: HashSet<PolicyId>,
    pub satisfied_forbids: HashSet<PolicyId>,
    pub false_forbids: HashSet<PolicyId>,
    pub error_forbids: HashSet<PolicyId>,
    pub residual_forbids: HashSet<PolicyId>,
    pub residuals: Vec<TpeResidualPolicy>,
}

impl TpeResponse {
    pub(crate) fn from_inner(inner: TpeResponseInner) -> Result<Self, FfiError> {
        let decision = match inner.decision.as_deref() {
            Some("allow") => Some(Decision::Allow),
            Some("deny") => Some(Decision::Deny),
            Some(other) => return Err(FfiError::LeanDeserializationError(other.to_owned())),
            None => None,
        };
        let to_set = |s: Vec<String>| s.iter().map(PolicyId::new).collect();
        let residuals = inner
            .residuals
            .into_iter()
            .map(|r| TpeResidualPolicy {
                id: PolicyId::new(&r.id),
                effect: r.effect,
                residual: r.residual,
            })
            .collect();
        Ok(Self {
            decision,
            satisfied_permits: to_set(inner.satisfied_permits),
            false_permits: to_set(inner.false_permits),
            error_permits: to_set(inner.error_permits),
            residual_permits: to_set(inner.residual_permits),
            satisfied_forbids: to_set(inner.satisfied_forbids),
            false_forbids: to_set(inner.false_forbids),
            error_forbids: to_set(inner.error_forbids),
            residual_forbids: to_set(inner.residual_forbids),
            residuals,
        })
    }
}

mod convert {
    use super::*;
    use cedar_policy_core::pst;
    use smol_str::SmolStr;
    use std::collections::BTreeMap;
    use std::sync::Arc;

    /// Error converting a Lean residual to a PST expression
    #[derive(Debug, thiserror::Error)]
    pub enum ResidualConversionError {
        #[error("failed to convert value: {0}")]
        ValueConversion(String),
        #[error("failed to convert pattern element: invalid char codepoint {0}")]
        InvalidChar(u32),
        #[error("unsupported extension function with {0} args")]
        UnsupportedExtArity(usize),
    }

    fn entity_type_name_to_pst_name(etn: &cedar_policy::EntityTypeName) -> pst::Name {
        pst::Name {
            id: pst::Id::new(etn.basename()).expect("valid basename"),
            namespace: std::sync::Arc::new(
                etn.namespace_components()
                    .map(|c| pst::Id::new(c).expect("valid namespace component"))
                    .collect(),
            ),
        }
    }

    fn convert_value(v: super::super::Value) -> Result<pst::Expr, ResidualConversionError> {
        let rexpr: cedar_policy::RestrictedExpression =
            v.try_into().map_err(|e: Box<dyn miette::Diagnostic>| {
                ResidualConversionError::ValueConversion(e.to_string())
            })?;
        let ast_expr: &cedar_policy_core::ast::Expr = rexpr.as_ref().as_ref();
        pst::Expr::try_from(ast_expr.clone())
            .map_err(|e| ResidualConversionError::ValueConversion(e.to_string()))
    }

    fn convert_var(v: Var) -> pst::Var {
        match v {
            Var::Principal => pst::Var::Principal,
            Var::Action => pst::Var::Action,
            Var::Resource => pst::Var::Resource,
            Var::Context => pst::Var::Context,
        }
    }

    fn convert_pattern(
        p: Vec<super::super::PatElem>,
    ) -> Result<Vec<pst::PatternElem>, ResidualConversionError> {
        p.into_iter()
            .map(|e| match e {
                super::super::PatElem::Star => Ok(pst::PatternElem::Wildcard),
                super::super::PatElem::Char { c } => char::try_from(c)
                    .map(pst::PatternElem::Char)
                    .map_err(|_| ResidualConversionError::InvalidChar(c)),
            })
            .collect()
    }

    fn convert_ext_fun(
        xfn: ExtFun,
        args: Vec<Residual>,
    ) -> Result<pst::Expr, ResidualConversionError> {
        let pst_args: Vec<Arc<pst::Expr>> = args
            .into_iter()
            .map(|a| Ok(Arc::new(convert_residual(a)?)))
            .collect::<Result<Vec<_>, ResidualConversionError>>()?;

        match pst_args.len() {
            1 => {
                let op = match xfn {
                    ExtFun::Decimal => pst::UnaryOp::Decimal,
                    ExtFun::Ip => pst::UnaryOp::Ip,
                    ExtFun::Datetime => pst::UnaryOp::Datetime,
                    ExtFun::Duration => pst::UnaryOp::Duration,
                    ExtFun::IsIpv4 => pst::UnaryOp::IsIPv4,
                    ExtFun::IsIpv6 => pst::UnaryOp::IsIPV6,
                    ExtFun::IsLoopback => pst::UnaryOp::IsLoopback,
                    ExtFun::IsMulticast => pst::UnaryOp::IsMulticast,
                    ExtFun::ToDate => pst::UnaryOp::ToDate,
                    ExtFun::ToTime => pst::UnaryOp::ToTime,
                    ExtFun::ToMilliseconds => pst::UnaryOp::ToMilliseconds,
                    ExtFun::ToSeconds => pst::UnaryOp::ToSeconds,
                    ExtFun::ToMinutes => pst::UnaryOp::ToMinutes,
                    ExtFun::ToHours => pst::UnaryOp::ToHours,
                    ExtFun::ToDays => pst::UnaryOp::ToDays,
                    _ => return Err(ResidualConversionError::UnsupportedExtArity(1)),
                };
                #[expect(clippy::unwrap_used, reason = "length checked")]
                let expr = pst_args.into_iter().next().unwrap();
                Ok(pst::Expr::UnaryOp { op, expr })
            }
            2 => {
                let op = match xfn {
                    ExtFun::LessThan => pst::BinaryOp::DecimalLessThan,
                    ExtFun::LessThanOrEqual => pst::BinaryOp::DecimalLessEq,
                    ExtFun::GreaterThan => pst::BinaryOp::DecimalGreater,
                    ExtFun::GreaterThanOrEqual => pst::BinaryOp::DecimalGreaterEq,
                    ExtFun::IsInRange => pst::BinaryOp::IsInRange,
                    ExtFun::Offset => pst::BinaryOp::Offset,
                    ExtFun::DurationSince => pst::BinaryOp::DurationSince,
                    _ => return Err(ResidualConversionError::UnsupportedExtArity(2)),
                };
                let mut it = pst_args.into_iter();
                #[expect(clippy::unwrap_used, reason = "length checked")]
                let left = it.next().unwrap();
                #[expect(clippy::unwrap_used, reason = "length checked")]
                let right = it.next().unwrap();
                Ok(pst::Expr::BinaryOp { op, left, right })
            }
            n => Err(ResidualConversionError::UnsupportedExtArity(n)),
        }
    }

    fn convert_residual(r: Residual) -> Result<pst::Expr, ResidualConversionError> {
        match r {
            Residual::Val { v, .. } => convert_value(v),
            Residual::Var { v, .. } => Ok(pst::Expr::Var(convert_var(v))),
            Residual::Error { .. } => Ok(pst::Expr::ResidualError),
            Residual::Ite {
                cond,
                then_expr,
                else_expr,
                ..
            } => Ok(pst::Expr::IfThenElse {
                cond: Arc::new(convert_residual(*cond)?),
                then_expr: Arc::new(convert_residual(*then_expr)?),
                else_expr: Arc::new(convert_residual(*else_expr)?),
            }),
            Residual::And { a, b, .. } => Ok(pst::Expr::BinaryOp {
                op: pst::BinaryOp::And,
                left: Arc::new(convert_residual(*a)?),
                right: Arc::new(convert_residual(*b)?),
            }),
            Residual::Or { a, b, .. } => Ok(pst::Expr::BinaryOp {
                op: pst::BinaryOp::Or,
                left: Arc::new(convert_residual(*a)?),
                right: Arc::new(convert_residual(*b)?),
            }),
            Residual::UnaryApp {
                op: UnaryOp::Not,
                expr,
                ..
            } => Ok(pst::Expr::UnaryOp {
                op: pst::UnaryOp::Not,
                expr: Arc::new(convert_residual(*expr)?),
            }),
            Residual::UnaryApp {
                op: UnaryOp::Neg,
                expr,
                ..
            } => Ok(pst::Expr::UnaryOp {
                op: pst::UnaryOp::Neg,
                expr: Arc::new(convert_residual(*expr)?),
            }),
            Residual::UnaryApp {
                op: UnaryOp::IsEmpty,
                expr,
                ..
            } => Ok(pst::Expr::UnaryOp {
                op: pst::UnaryOp::IsEmpty,
                expr: Arc::new(convert_residual(*expr)?),
            }),
            Residual::UnaryApp {
                op: UnaryOp::Like { p },
                expr,
                ..
            } => Ok(pst::Expr::Like {
                expr: Arc::new(convert_residual(*expr)?),
                pattern: convert_pattern(p)?,
            }),
            Residual::UnaryApp {
                op: UnaryOp::Is { ety },
                expr,
                ..
            } => Ok(pst::Expr::Is {
                expr: Arc::new(convert_residual(*expr)?),
                entity_type: pst::EntityType(entity_type_name_to_pst_name(&ety)),
                in_expr: None,
            }),
            Residual::BinaryApp { op, a, b, .. } => {
                let pst_op = match op {
                    BinaryOp::Eq => pst::BinaryOp::Eq,
                    BinaryOp::Mem => pst::BinaryOp::In,
                    BinaryOp::HasTag => pst::BinaryOp::HasTag,
                    BinaryOp::GetTag => pst::BinaryOp::GetTag,
                    BinaryOp::Less => pst::BinaryOp::Less,
                    BinaryOp::LessEq => pst::BinaryOp::LessEq,
                    BinaryOp::Add => pst::BinaryOp::Add,
                    BinaryOp::Sub => pst::BinaryOp::Sub,
                    BinaryOp::Mul => pst::BinaryOp::Mul,
                    BinaryOp::Contains => pst::BinaryOp::Contains,
                    BinaryOp::ContainsAll => pst::BinaryOp::ContainsAll,
                    BinaryOp::ContainsAny => pst::BinaryOp::ContainsAny,
                };
                Ok(pst::Expr::BinaryOp {
                    op: pst_op,
                    left: Arc::new(convert_residual(*a)?),
                    right: Arc::new(convert_residual(*b)?),
                })
            }
            Residual::GetAttr { expr, attr, .. } => Ok(pst::Expr::GetAttr {
                expr: Arc::new(convert_residual(*expr)?),
                attr: SmolStr::new(attr),
            }),
            Residual::HasAttr { expr, attr, .. } => Ok(pst::Expr::HasAttr {
                expr: Arc::new(convert_residual(*expr)?),
                attrs: nonempty::NonEmpty::new(SmolStr::new(attr)),
            }),
            Residual::Set { ls, .. } => Ok(pst::Expr::Set(
                ls.into_iter()
                    .map(|r| Ok(Arc::new(convert_residual(r)?)))
                    .collect::<Result<Vec<_>, ResidualConversionError>>()?,
            )),
            Residual::Record { map, .. } => Ok(pst::Expr::Record(
                map.into_iter()
                    .map(|(k, v)| Ok((k, Arc::new(convert_residual(v)?))))
                    .collect::<Result<BTreeMap<_, _>, ResidualConversionError>>()?,
            )),
            Residual::Call { xfn, args, .. } => convert_ext_fun(xfn, args),
        }
    }

    impl TryFrom<Residual> for pst::Expr {
        type Error = ResidualConversionError;
        fn try_from(r: Residual) -> Result<Self, Self::Error> {
            convert_residual(r)
        }
    }
}

pub use convert::ResidualConversionError;
