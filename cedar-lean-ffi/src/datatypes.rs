use cedar_policy::{Decision, EntityId, EntityTypeName, EntityUid, PolicyId};
use num_bigint::ParseBigIntError;
use serde::{Deserialize, Deserializer};
use smol_str::SmolStr;
use thiserror::Error;

use std::char::CharTryFromError;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::str::FromStr;
use std::sync::Arc;

use crate::FfiError;

/*************************************** Lean return types ***************************************/

/// List type
#[derive(Debug, Deserialize)]
pub(crate) struct ListDef<T> {
    pub(crate) l: Vec<T>,
}

/// Set Type
#[derive(Debug, Deserialize)]
pub(crate) struct SetDef<T> {
    pub(crate) mk: ListDef<T>,
}

/// Lean type: Except String T
#[derive(Debug, Deserialize)]
pub(crate) enum ResultDef<T> {
    /// Successful execution
    #[serde(rename = "ok")]
    Ok(T),
    /// Failure case
    #[serde(rename = "error")]
    Error(String),
}

impl<T> ResultDef<T> {
    pub fn to_result(def: ResultDef<T>) -> Result<T, String> {
        match def {
            ResultDef::Ok(t) => Ok(t),
            ResultDef::Error(s) => Err(s),
        }
    }
}

#[derive(Debug, Deserialize)]
pub(crate) struct TimedDef<T> {
    pub(crate) data: T,
    pub(crate) duration: u128,
}

/// Authorization Response
#[derive(Debug, Deserialize)]
pub(crate) struct AuthorizationResponseInner {
    pub(crate) decision: String,
    #[serde(rename = "determiningPolicies")]
    pub(crate) determining_policies: SetDef<String>,
    #[serde(rename = "erroringPolicies")]
    pub(crate) erroring_policies: SetDef<String>,
}

#[derive(Debug, Deserialize)]
pub(crate) enum OptionDef<T> {
    #[serde(rename = "none")]
    None,
    #[serde(rename = "some")]
    Some(T),
}

impl<T> From<OptionDef<T>> for Option<T> {
    fn from(def: OptionDef<T>) -> Self {
        match def {
            OptionDef::Some(t) => Self::Some(t),
            OptionDef::None => Self::None,
        }
    }
}

#[derive(Debug, Deserialize)]
pub(crate) struct NameDef {
    id: String,
    path: Vec<String>,
}

#[derive(Debug, Deserialize)]
pub(crate) struct EntityUidDef {
    #[serde(deserialize_with = "deserialize_entity_type_name")]
    ty: EntityTypeName,
    eid: String,
}

/********************************** Deserialization Helpers **********************************/
// Helper function to deserialize OptionDef into Option
fn deserialize_option_def<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
    OptionDef<T>: Deserialize<'de>,
{
    Ok(OptionDef::deserialize(deserializer)?.into())
}

// Helper function to deserialize NameDef into an EntityTypeName
fn deserialize_entity_type_name<'de, D>(deserializer: D) -> Result<EntityTypeName, D::Error>
where
    D: Deserializer<'de>,
{
    let name_def = NameDef::deserialize(deserializer)?;
    let mut result = name_def.path.join("::");
    if !result.is_empty() {
        result.push_str("::");
    }
    result.push_str(&name_def.id);
    EntityTypeName::from_str(&result).map_err(serde::de::Error::custom)
}

// Helper function to deserialize EntityUidDef into an EntityUid
fn deserialize_entity_uid<'de, D>(deserializer: D) -> Result<EntityUid, D::Error>
where
    D: Deserializer<'de>,
{
    let euid_def = EntityUidDef::deserialize(deserializer)?;
    let eid = EntityId::new(euid_def.eid);
    Ok(EntityUid::from_type_name_and_id(euid_def.ty, eid))
}

/********************************** Publicly Exported Types **********************************/

#[derive(Debug)]
pub struct TimedResult<T> {
    pub(crate) result: T,
    pub(crate) duration: u128,
}

impl<T> TimedResult<T> {
    pub(crate) fn from_def(tdef: TimedDef<T>) -> Self {
        Self {
            result: tdef.data,
            duration: tdef.duration,
        }
    }

    /// The result of running the code
    pub fn result(&self) -> &T {
        &self.result
    }

    pub fn take_result(self) -> T {
        self.result
    }

    /// The duration the code ran for
    pub fn duration(&self) -> u128 {
        self.duration
    }

    pub(crate) fn transform<U, F>(self, f: F) -> TimedResult<U>
    where
        F: FnOnce(T) -> U,
    {
        TimedResult {
            result: f(self.result),
            duration: self.duration,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthorizationResponse {
    decision: Decision,
    determining: HashSet<PolicyId>,
    erroring: HashSet<PolicyId>,
}

impl AuthorizationResponse {
    pub(crate) fn from_inner(inner: AuthorizationResponseInner) -> Result<Self, FfiError> {
        let decision = match inner.decision.as_str() {
            "allow" => Decision::Allow,
            "deny" => Decision::Deny,
            _ => return Err(FfiError::LeanDeserializationError(inner.decision)),
        };
        let determining = inner
            .determining_policies
            .mk
            .l
            .iter()
            .map(PolicyId::new)
            .collect();
        let erroring = inner
            .erroring_policies
            .mk
            .l
            .iter()
            .map(PolicyId::new)
            .collect();
        Ok(Self {
            decision,
            determining,
            erroring,
        })
    }

    pub fn decision(&self) -> Decision {
        self.decision
    }

    pub fn determining_policies(&self) -> &HashSet<PolicyId> {
        &self.determining
    }

    pub fn erroring_policies(&self) -> &HashSet<PolicyId> {
        &self.erroring
    }
}

/// Validation Response
#[derive(Debug, Deserialize, PartialEq)]
pub enum ValidationResponse {
    /// Successful validation
    #[serde(rename = "ok")]
    Ok(()),
    /// Validation error case
    #[serde(rename = "error")]
    Error(String),
}

/********************************** SymCC Terms **********************************/

#[derive(Debug, Deserialize)]
pub struct Uuf {
    pub id: String,
    pub arg: TermType,
    pub out: TermType,
}

#[derive(Debug, Deserialize)]
pub enum ExtOp {
    #[serde(rename = "decimal.val")]
    DecimalVal,
    #[serde(rename = "ipaddr.isv4")]
    IPaddrIsV4,
    #[serde(rename = "ipaddr.addrV4")]
    IPaddrAddrV4,
    #[serde(rename = "ipaddr.prefixV4")]
    IPaddrPrefixV4,
    #[serde(rename = "ipaddr.addrV6")]
    IPaddrAddrV6,
    #[serde(rename = "ipaddr.prefixV6")]
    IPaddrPrefixV6,
    #[serde(rename = "datetime.val")]
    DatetimeVal,
    #[serde(rename = "datetime.ofBitVec")]
    DatetimeOfBitVec,
    #[serde(rename = "duration.val")]
    DurationVal,
    #[serde(rename = "duration.ofBitVec")]
    DurationOfBitVec,
}

#[derive(Debug, Deserialize)]
pub enum PatElem {
    #[serde(rename = "star")]
    Star,
    #[serde(rename = "justChar")]
    Char { c: u32 },
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Op {
    Not,
    And,
    Or,
    Eq,
    Ite,
    Uuf(Uuf),
    Bvneg,
    Bvadd,
    Bvsub,
    Bvmul,
    Bvsdiv,
    Bvudiv,
    Bvsrem,
    Bvsmod,
    Bvumod,
    Bvshl,
    Bvlshr,
    Bvslt,
    Bvsle,
    Bvult,
    Bvule,
    Bvnego,
    Bvsaddo,
    Bvssubo,
    Bvsmulo,
    ZeroExtend(u8),
    #[serde(rename = "set.member")]
    SetMember,
    #[serde(rename = "set.subset")]
    SetSubset,
    #[serde(rename = "set.inter")]
    SetInter,
    #[serde(rename = "option.get")]
    OptionGet,
    #[serde(rename = "record.get")]
    RecordGet(String),
    #[serde(rename = "string.like")]
    StringLike(Vec<PatElem>),
    Ext(ExtOp),
}

#[derive(Debug, Deserialize)]
pub struct Bitvec {
    pub width: u8,
    pub val: String,
}

#[derive(Debug, Deserialize)]
pub struct Decimal(pub i64);

#[derive(Debug, Deserialize)]
pub struct Cidr {
    pub addr: Bitvec,
    #[serde(rename = "pre", deserialize_with = "deserialize_option_def")]
    pub prefix: Option<Bitvec>,
}

#[derive(Debug, Deserialize)]
pub enum IpAddr {
    V4(Cidr),
    V6(Cidr),
}

#[derive(Debug, Deserialize)]
pub struct Datetime {
    pub val: i64,
}

#[derive(Debug, Deserialize)]
pub struct Duration {
    pub val: i64,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ExtType {
    IpAddr,
    Decimal,
    Datetime,
    Duration,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum TermPrimType {
    Bool,
    Bitvec {
        n: u8,
    },
    String,
    Entity {
        #[serde(deserialize_with = "deserialize_entity_type_name")]
        ety: EntityTypeName,
    },
    Ext {
        xty: ExtType,
    },
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum TermType {
    Prim { pty: TermPrimType },
    Option { ty: Box<TermType> },
    Set { ty: Box<TermType> },
    Record { rty: Vec<(String, TermType)> },
}

#[derive(Debug, Deserialize)]
pub struct TermVar {
    pub id: String,
    pub ty: TermType,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Ext {
    Decimal { d: Decimal },
    Ipaddr { ip: IpAddr },
    Datetime { dt: Datetime },
    Duration { d: Duration },
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum TermPrim {
    Bool(bool),
    Bitvec(Bitvec),
    String(String),
    Entity(#[serde(deserialize_with = "deserialize_entity_uid")] EntityUid),
    Ext(Ext),
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Term {
    Prim(TermPrim),
    Var(TermVar),
    None(TermType),
    Some(Box<Term>),
    #[serde(rename_all = "camelCase")]
    Set {
        elts: Vec<Term>,
        elts_ty: TermType,
    },
    Record(Vec<(String, Term)>),
    #[serde(rename_all = "camelCase")]
    App {
        op: Op,
        args: Vec<Term>,
        ret_ty: TermType,
    },
}

impl From<TermVar> for cedar_policy_symcc::TermVar {
    fn from(value: TermVar) -> Self {
        Self {
            id: value.id,
            ty: value.ty.into(),
        }
    }
}

impl From<Uuf> for cedar_policy_symcc::Uuf {
    fn from(value: Uuf) -> Self {
        Self {
            id: value.id,
            arg: value.arg.into(),
            out: value.out.into(),
        }
    }
}

#[derive(Debug, Error)]
pub enum TermConversionError {
    #[error(transparent)]
    CharConversion(#[from] CharTryFromError),
    #[error(transparent)]
    ParseBigInt(#[from] ParseBigIntError),
    #[error(transparent)]
    ConstructBV(#[from] cedar_policy_symcc::result::Error),
}

impl TryFrom<PatElem> for cedar_policy_core::ast::PatternElem {
    type Error = TermConversionError;

    fn try_from(value: PatElem) -> Result<Self, Self::Error> {
        Ok(match value {
            PatElem::Char { c } => Self::Char(c.try_into()?),
            PatElem::Star => Self::Wildcard,
        })
    }
}

impl From<ExtOp> for cedar_policy_symcc::ExtOp {
    fn from(value: ExtOp) -> Self {
        match value {
            ExtOp::DecimalVal => Self::DecimalVal,
            ExtOp::IPaddrIsV4 => Self::IpaddrIsV4,
            ExtOp::IPaddrAddrV4 => Self::IpaddrAddrV4,
            ExtOp::IPaddrPrefixV4 => Self::IpaddrPrefixV4,
            ExtOp::IPaddrAddrV6 => Self::IpaddrAddrV6,
            ExtOp::IPaddrPrefixV6 => Self::IpaddrPrefixV6,
            ExtOp::DatetimeVal => Self::DatetimeVal,
            ExtOp::DatetimeOfBitVec => Self::DatetimeOfBitVec,
            ExtOp::DurationVal => Self::DurationVal,
            ExtOp::DurationOfBitVec => Self::DurationOfBitVec,
        }
    }
}

impl TryFrom<Op> for cedar_policy_symcc::Op {
    type Error = TermConversionError;

    fn try_from(value: Op) -> Result<Self, Self::Error> {
        Ok(match value {
            Op::Not => Self::Not,
            Op::And => Self::And,
            Op::Or => Self::Or,
            Op::Eq => Self::Eq,
            Op::Ite => Self::Ite,
            Op::Uuf(uuf) => Self::Uuf(Arc::new(uuf.into())),
            Op::Bvneg => Self::Bvneg,
            Op::Bvadd => Self::Bvadd,
            Op::Bvsub => Self::Bvsub,
            Op::Bvmul => Self::Bvmul,
            Op::Bvsdiv => Self::Bvsdiv,
            Op::Bvudiv => Self::Bvudiv,
            Op::Bvsrem => Self::Bvsrem,
            Op::Bvsmod => Self::Bvsmod,
            Op::Bvumod => Self::Bvumod,
            Op::Bvshl => Self::Bvshl,
            Op::Bvlshr => Self::Bvlshr,
            Op::Bvslt => Self::Bvslt,
            Op::Bvsle => Self::Bvsle,
            Op::Bvult => Self::Bvult,
            Op::Bvule => Self::Bvule,
            Op::Bvnego => Self::Bvnego,
            Op::Bvsaddo => Self::Bvsaddo,
            Op::Bvssubo => Self::Bvssubo,
            Op::Bvsmulo => Self::Bvsmulo,
            Op::ZeroExtend(u) => Self::ZeroExtend(u.into()),
            Op::SetMember => Self::SetMember,
            Op::SetSubset => Self::SetSubset,
            Op::SetInter => Self::SetInter,
            Op::OptionGet => Self::OptionGet,
            Op::RecordGet(a) => Self::RecordGet(a.into()),
            Op::StringLike(pats) => Self::StringLike(
                cedar_policy_core::ast::Pattern::from_iter(
                    pats.into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<_>, _>>()?,
                )
                .into(),
            ),
            Op::Ext(op) => Self::Ext(op.into()),
        })
    }
}

impl TryFrom<Bitvec> for cedar_policy_symcc::BitVec {
    type Error = TermConversionError;

    fn try_from(value: Bitvec) -> Result<Self, Self::Error> {
        Ok(Self::of_nat(value.width.into(), value.val.parse()?)?)
    }
}

impl TryFrom<Ext> for cedar_policy_symcc::Ext {
    type Error = TermConversionError;
    fn try_from(value: Ext) -> Result<Self, Self::Error> {
        Ok(match value {
            Ext::Datetime { dt } => Self::Datetime { dt: dt.val.into() },
            Ext::Duration { d } => Self::Duration { d: d.val.into() },
            Ext::Decimal { d } => Self::Decimal {
                d: cedar_policy_symcc::extension_types::decimal::Decimal(d.0),
            },
            Ext::Ipaddr {
                ip: IpAddr::V4(cidr),
            } => Self::Ipaddr {
                ip: cedar_policy_symcc::extension_types::ipaddr::IPNet::V4(
                    cedar_policy_symcc::extension_types::ipaddr::CIDRv4 {
                        addr: cedar_policy_symcc::extension_types::ipaddr::IPv4Addr {
                            val: cidr.addr.try_into()?,
                        },
                        prefix: cedar_policy_symcc::extension_types::ipaddr::IPv4Prefix {
                            val: cidr.prefix.map(TryInto::try_into).transpose()?,
                        },
                    },
                ),
            },
            Ext::Ipaddr {
                ip: IpAddr::V6(cidr),
            } => Self::Ipaddr {
                ip: cedar_policy_symcc::extension_types::ipaddr::IPNet::V6(
                    cedar_policy_symcc::extension_types::ipaddr::CIDRv6 {
                        addr: cedar_policy_symcc::extension_types::ipaddr::IPv6Addr {
                            val: cidr.addr.try_into()?,
                        },
                        prefix: cedar_policy_symcc::extension_types::ipaddr::IPv6Prefix {
                            val: cidr.prefix.map(TryInto::try_into).transpose()?,
                        },
                    },
                ),
            },
        })
    }
}

impl TryFrom<TermPrim> for cedar_policy_symcc::TermPrim {
    type Error = TermConversionError;
    fn try_from(value: TermPrim) -> Result<Self, Self::Error> {
        Ok(match value {
            TermPrim::Bitvec(bv) => Self::Bitvec(bv.try_into()?),
            TermPrim::Bool(b) => Self::Bool(b),
            TermPrim::Entity(uid) => Self::Entity(uid),
            TermPrim::Ext(ext) => Self::Ext(ext.try_into()?),
            TermPrim::String(s) => Self::String(s.into()),
        })
    }
}

impl TryFrom<Term> for cedar_policy_symcc::Term {
    type Error = TermConversionError;
    fn try_from(value: Term) -> Result<Self, Self::Error> {
        Ok(match value {
            Term::App { op, args, ret_ty } => Self::App {
                op: op.try_into()?,
                args: Arc::new(
                    args.into_iter()
                        .map(|t| Self::try_from(t))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                ret_ty: ret_ty.into(),
            },
            Term::None(ty) => Self::None(ty.into()),
            Term::Prim(prim) => Self::Prim(prim.try_into()?),
            Term::Record(r) => Self::Record(Arc::new(
                r.into_iter()
                    .map(|(a, t)| Ok((SmolStr::from(a), Self::try_from(t)?)))
                    .collect::<Result<BTreeMap<SmolStr, Self>, Self::Error>>()?,
            )),
            Term::Set { elts, elts_ty } => Self::Set {
                elts: Arc::new(
                    elts.into_iter()
                        .map(|t| Self::try_from(t))
                        .collect::<Result<BTreeSet<Self>, _>>()?,
                ),
                elts_ty: elts_ty.into(),
            },
            Term::Some(term) => Self::Some(Arc::new((*term).try_into()?)),
            Term::Var(var) => Self::Var(var.into()),
        })
    }
}

impl From<ExtType> for cedar_policy_symcc::ExtType {
    fn from(value: ExtType) -> Self {
        match value {
            ExtType::IpAddr => Self::IpAddr,
            ExtType::Decimal => Self::Decimal,
            ExtType::Datetime => Self::DateTime,
            ExtType::Duration => Self::Duration,
        }
    }
}

impl From<TermType> for cedar_policy_symcc::TermType {
    fn from(value: TermType) -> Self {
        match value {
            TermType::Option { ty } => Self::Option {
                ty: Arc::new((*ty).into()),
            },
            TermType::Prim {
                pty: TermPrimType::Bitvec { n },
            } => Self::Bitvec { n: n.into() },
            TermType::Prim {
                pty: TermPrimType::Bool,
            } => Self::Bool,
            TermType::Prim {
                pty: TermPrimType::Entity { ety },
            } => Self::Entity { ety },
            TermType::Prim {
                pty: TermPrimType::Ext { xty },
            } => Self::Ext { xty: xty.into() },
            TermType::Prim {
                pty: TermPrimType::String,
            } => Self::String,
            TermType::Record { rty } => Self::Record {
                rty: Arc::new(BTreeMap::from_iter(
                    rty.into_iter().map(|(a, ty)| (a.into(), ty.into())),
                )),
            },
            TermType::Set { ty } => Self::Set {
                ty: Arc::new((*ty).into()),
            },
        }
    }
}
