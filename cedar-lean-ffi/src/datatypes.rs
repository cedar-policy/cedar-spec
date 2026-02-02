use cedar_policy::{Decision, EntityId, EntityTypeName, ParseErrors, PolicyId, RestrictedExpression};
use cedar_policy_core::ast::Name;
use num_bigint::ParseBigIntError;
use serde::{Deserialize, Serialize};
use serde_with::{serde_as, TryFromInto};
use smol_str::SmolStr;
use thiserror::Error;

use std::char::CharTryFromError;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::num::{NonZeroU8, NonZeroU32};
use std::str::FromStr;
use std::sync::Arc;

use crate::FfiError;

/*************************************** Lean return types ***************************************/

/// List type
#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct ListDef<T> {
    pub(crate) l: Vec<T>,
}

/// Set Type
#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct SetDef<T> {
    pub(crate) mk: ListDef<T>,
}

/// Lean type: Except String T
#[derive(Debug, Deserialize, Serialize)]
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

#[derive(Debug, Deserialize, Serialize)]
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub(crate) struct NameDef {
    id: SmolStr,
    path: Vec<SmolStr>,
}

impl TryFrom<NameDef> for EntityTypeName {
    type Error = ParseErrors;
    fn try_from(name: NameDef) -> Result<Self, Self::Error> {
        let mut result = name.path.join("::");
        if !result.is_empty() {
            result.push_str("::");
        }
        result.push_str(&name.id);
        EntityTypeName::from_str(&result)
    }
}

impl From<EntityTypeName> for NameDef {
    fn from(etn: EntityTypeName) -> Self {
        Self {
            id: SmolStr::new(etn.basename()),
            path: etn.namespace_components().map(SmolStr::new).collect(),
        }
    }
}

#[serde_as]
#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EntityUid {
    #[serde_as(as = "TryFromInto<NameDef>")]
    ty: EntityTypeName,
    eid: SmolStr,
}

impl From<EntityUid> for cedar_policy::EntityUid {
    fn from(euid: EntityUid) -> Self {
        let eid = EntityId::new(euid.eid);
        cedar_policy::EntityUid::from_type_name_and_id(euid.ty, eid)
    }
}

impl From<cedar_policy::EntityUid> for EntityUid {
    fn from(euid: cedar_policy::EntityUid) -> Self {
        Self {
            ty: euid.type_name().clone(),
            eid: euid.id().unescaped().into(),
        }
    }
}

impl std::fmt::Display for EntityUid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        cedar_policy::EntityUid::from(self.clone()).fmt(f)
    }
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
    pub id: SmolStr,
    pub arg: TermType,
    pub out: TermType,
}

#[derive(Debug, Deserialize)]
pub enum ExtOp {
    #[serde(rename = "decimal.val")]
    DecimalVal,
    #[serde(rename = "ipaddr.isV4")]
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
    RecordGet(SmolStr),
    #[serde(rename = "string.like")]
    StringLike(Vec<PatElem>),
    Ext(ExtOp),
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Bitvec {
    #[serde(rename = "size")]
    pub width: u8,
    /// String representation of the bitvector value (as Lean `Nat`)
    #[serde(rename = "value")]
    pub val: String,
}

impl Bitvec {
    /// Assuming the `Bitvec` is (up to) 64-bit, get the value as a `u64`
    ///
    /// Panics if the `Bitvec` was larger than 64-bit
    fn as_u64(&self) -> u64 {
        assert!(self.width <= 64, "width was too large: {}", self.width);
        self.val.parse().expect("should be a valid u64 value")
    }

    /// Assuming the `Bitvec` is 128-bit, get the value as a `u128`
    ///
    /// Panics if the `Bitvec` was not 128-bit
    fn as_u128(&self) -> u128 {
        assert!(self.width <= 128, "width was too large: {}", self.width);
        self.val.parse().expect("should be a valid u128 value")
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Decimal(pub i64);

impl From<Decimal> for RestrictedExpression {
    fn from(decimal: Decimal) -> Self {
        // note this assumes the Lean represents the decimal value `v` as the integer `10000 * v`
        let neg = if decimal.0 < 0 { "-" } else { "" };
        let absval = i64::abs(decimal.0);
        let left = absval / 10000;
        let right = absval % 10000;
        let right = if right < 10 {
            format!(".000{right}")
        } else if right < 100 {
            format!(".00{right}")
        } else if right < 1000 {
            format!(".0{right}")
        } else {
            format!(".{right}")
        };
        RestrictedExpression::new_decimal(format!("{neg}{left}{right}"))
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Cidr {
    pub addr: Bitvec,
    #[serde(rename = "pre")]
    pub prefix: Option<Bitvec>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum IpAddr {
    V4(Cidr),
    V6(Cidr),
}

impl From<IpAddr> for RestrictedExpression {
    fn from(ip: IpAddr) -> Self {
        match ip {
            IpAddr::V4(cidr) => {
                let addr = cidr.addr.as_u64();
                let mut addr = format!(
                    "{a0}.{a1}.{a2}.{a3}",
                    a0 = (addr >> 24) & 0xFF,
                    a1 = (addr >> 16) & 0xFF,
                    a2 = (addr >> 8) & 0xFF,
                    a3 = addr & 0xFF,
                );
                if let Some(prefix) = cidr.prefix {
                    addr.push_str(&format!("/{}", prefix.as_u64()));
                }
                RestrictedExpression::new_ip(addr)
            }
            IpAddr::V6(cidr) => {
                let addr = cidr.addr.as_u128();
                let mut addr = format!(
                    "{a0:x}:{a1:x}:{a2:x}:{a3:x}:{a4:x}:{a5:x}:{a6:x}:{a7:x}",
                    a0 = (addr >> 112) & 0xFFFF,
                    a1 = (addr >> 96) & 0xFFFF,
                    a2 = (addr >> 80) & 0xFFFF,
                    a3 = (addr >> 64) & 0xFFFF,
                    a4 = (addr >> 48) & 0xFFFF,
                    a5 = (addr >> 32) & 0xFFFF,
                    a6 = (addr >> 16) & 0xFFFF,
                    a7 = addr & 0xFFFF,
                );
                if let Some(prefix) = cidr.prefix {
                    addr.push_str(&format!("/{}", prefix.as_u64()));
                }
                RestrictedExpression::new_ip(addr)
            }
        }
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Datetime {
    pub val: i64,
}

impl TryFrom<Datetime> for RestrictedExpression {
    type Error = cedar_policy_core::parser::err::ParseErrors;
    fn try_from(dt: Datetime) -> Result<Self, Self::Error> {
        // note this assumes the Lean represents datetimes as milliseconds since Unix epoch
        let epoch = cedar_policy_core::ast::RestrictedExpr::call_extension_fn(
            Name::parse_unqualified_name("datetime")?,
            [cedar_policy_core::ast::RestrictedExpr::val("1970-01-01")],
        );
        let millis_since_epoch = cedar_policy_core::ast::RestrictedExpr::call_extension_fn(
            Name::parse_unqualified_name("duration")?,
            [cedar_policy_core::ast::RestrictedExpr::val(format!(
                "{}ms",
                dt.val
            ))],
        );
        let core_rexpr = cedar_policy_core::ast::RestrictedExpr::call_extension_fn(
            Name::parse_unqualified_name("offset")?,
            [epoch, millis_since_epoch],
        );
        Ok(core_rexpr.into())
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Duration {
    pub val: i64,
}

impl From<Duration> for RestrictedExpression {
    fn from(dur: Duration) -> Self {
        // note this assumes the Lean represents durations as milliseconds
        RestrictedExpression::new_duration(format!("{}ms", dur.val))
    }
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ExtType {
    IpAddr,
    Decimal,
    Datetime,
    Duration,
}

#[serde_as]
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum TermPrimType {
    Bool,
    Bitvec {
        n: NonZeroU8,
    },
    String,
    Entity {
        #[serde_as(as = "TryFromInto<NameDef>")]
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
    Record { rty: Vec<(SmolStr, TermType)> },
}

#[derive(Debug, Deserialize)]
pub struct TermVar {
    pub id: SmolStr,
    pub ty: TermType,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Ext {
    Decimal { d: Decimal },
    Ipaddr { ip: IpAddr },
    Datetime { dt: Datetime },
    Duration { dur: Duration },
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum TermPrim {
    Bool(bool),
    Bitvec(Bitvec),
    String(SmolStr),
    Entity(EntityUid),
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
    Record(Vec<(SmolStr, Term)>),
    #[serde(rename_all = "camelCase")]
    App {
        op: Op,
        args: Vec<Term>,
        ret_ty: TermType,
    },
}

impl From<TermVar> for cedar_policy_symcc::term::TermVar {
    fn from(value: TermVar) -> Self {
        Self {
            id: value.id,
            ty: value.ty.into(),
        }
    }
}

impl From<Uuf> for cedar_policy_symcc::op::Uuf {
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
    ConstructBV(#[from] cedar_policy_symcc::err::BitVecError),
    #[error("bitvec had zero width")]
    ZeroWidthBV,
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

impl From<ExtOp> for cedar_policy_symcc::op::ExtOp {
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

impl TryFrom<Op> for cedar_policy_symcc::op::Op {
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
            Op::RecordGet(a) => Self::RecordGet(a),
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

impl TryFrom<Bitvec> for cedar_policy_symcc::bitvec::BitVec {
    type Error = TermConversionError;

    fn try_from(value: Bitvec) -> Result<Self, Self::Error> {
        let width = NonZeroU32::new(value.width.into()).ok_or(TermConversionError::ZeroWidthBV)?;
        Ok(Self::of_nat(width, value.val.parse()?))
    }
}

impl TryFrom<Ext> for cedar_policy_symcc::ext::Ext {
    type Error = TermConversionError;
    fn try_from(value: Ext) -> Result<Self, Self::Error> {
        Ok(match value {
            Ext::Datetime { dt } => Self::Datetime { dt: dt.val.into() },
            Ext::Duration { dur } => Self::Duration { d: dur.val.into() },
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

impl TryFrom<TermPrim> for cedar_policy_symcc::term::TermPrim {
    type Error = TermConversionError;
    fn try_from(value: TermPrim) -> Result<Self, Self::Error> {
        Ok(match value {
            TermPrim::Bitvec(bv) => Self::Bitvec(bv.try_into()?),
            TermPrim::Bool(b) => Self::Bool(b),
            TermPrim::Entity(uid) => Self::Entity(uid.into()),
            TermPrim::Ext(ext) => Self::Ext(ext.try_into()?),
            TermPrim::String(s) => Self::String(s),
        })
    }
}

impl TryFrom<Term> for cedar_policy_symcc::term::Term {
    type Error = TermConversionError;
    fn try_from(value: Term) -> Result<Self, Self::Error> {
        Ok(match value {
            Term::App { op, args, ret_ty } => Self::App {
                op: op.try_into()?,
                args: Arc::new(
                    args.into_iter()
                        .map(Self::try_from)
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                ret_ty: ret_ty.into(),
            },
            Term::None(ty) => Self::None(ty.into()),
            Term::Prim(prim) => Self::Prim(prim.try_into()?),
            Term::Record(r) => Self::Record(Arc::new(
                r.into_iter()
                    .map(|(a, t)| Ok((a, Self::try_from(t)?)))
                    .collect::<Result<BTreeMap<SmolStr, Self>, Self::Error>>()?,
            )),
            Term::Set { elts, elts_ty } => Self::Set {
                elts: Arc::new(
                    elts.into_iter()
                        .map(Self::try_from)
                        .collect::<Result<BTreeSet<Self>, _>>()?,
                ),
                elts_ty: elts_ty.into(),
            },
            Term::Some(term) => Self::Some(Arc::new((*term).try_into()?)),
            Term::Var(var) => Self::Var(var.into()),
        })
    }
}

impl From<ExtType> for cedar_policy_symcc::type_abbrevs::ExtType {
    fn from(value: ExtType) -> Self {
        match value {
            ExtType::IpAddr => Self::IpAddr,
            ExtType::Decimal => Self::Decimal,
            ExtType::Datetime => Self::DateTime,
            ExtType::Duration => Self::Duration,
        }
    }
}

impl From<TermType> for cedar_policy_symcc::term_type::TermType {
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
                    rty.into_iter().map(|(a, ty)| (a, ty.into())),
                )),
            },
            TermType::Set { ty } => Self::Set {
                ty: Arc::new((*ty).into()),
            },
        }
    }
}

impl From<cedar_policy_symcc::type_abbrevs::ExtType> for ExtType {
    fn from(value: cedar_policy_symcc::type_abbrevs::ExtType) -> Self {
        match value {
            cedar_policy_symcc::type_abbrevs::ExtType::IpAddr => Self::IpAddr,
            cedar_policy_symcc::type_abbrevs::ExtType::Decimal => Self::Decimal,
            cedar_policy_symcc::type_abbrevs::ExtType::DateTime => Self::Datetime,
            cedar_policy_symcc::type_abbrevs::ExtType::Duration => Self::Duration,
        }
    }
}

impl From<cedar_policy_symcc::term_type::TermType> for TermType {
    fn from(value: cedar_policy_symcc::term_type::TermType) -> Self {
        match value {
            cedar_policy_symcc::term_type::TermType::Option { ty } => Self::Option {
                ty: Box::new(Arc::unwrap_or_clone(ty).into()),
            },
            cedar_policy_symcc::term_type::TermType::Bitvec { n } => Self::Prim {
                // PANIC SAFETY: `n` should not overflow `u8`
                pty: TermPrimType::Bitvec {
                    n: n.try_into().unwrap(),
                },
            },
            cedar_policy_symcc::term_type::TermType::Bool => Self::Prim {
                pty: TermPrimType::Bool,
            },
            cedar_policy_symcc::term_type::TermType::Entity { ety } => Self::Prim {
                pty: TermPrimType::Entity { ety },
            },
            cedar_policy_symcc::term_type::TermType::Ext { xty } => Self::Prim {
                pty: TermPrimType::Ext { xty: xty.into() },
            },
            cedar_policy_symcc::term_type::TermType::String => Self::Prim {
                pty: TermPrimType::String,
            },
            cedar_policy_symcc::term_type::TermType::Record { rty } => Self::Record {
                rty: Arc::unwrap_or_clone(rty)
                    .into_iter()
                    .map(|(a, ty)| (a, ty.into()))
                    .collect(),
            },
            cedar_policy_symcc::term_type::TermType::Set { ty } => Self::Set {
                ty: Box::new(Arc::unwrap_or_clone(ty).into()),
            },
        }
    }
}

impl From<cedar_policy_symcc::bitvec::BitVec> for Bitvec {
    fn from(value: cedar_policy_symcc::bitvec::BitVec) -> Self {
        Self {
            // PANIC SAFETY: `value.width()` should not overflow `u8`
            width: value.width().get().try_into().unwrap(),
            val: value.to_nat().to_string(),
        }
    }
}

impl From<cedar_policy_symcc::term::TermPrim> for TermPrim {
    fn from(value: cedar_policy_symcc::term::TermPrim) -> Self {
        match value {
            cedar_policy_symcc::term::TermPrim::Bitvec(bv) => Self::Bitvec(Bitvec {
                width: bv.width().get().try_into().unwrap(),
                val: bv.to_nat().to_string(),
            }),
            cedar_policy_symcc::term::TermPrim::Bool(b) => Self::Bool(b),
            cedar_policy_symcc::term::TermPrim::Entity(uid) => Self::Entity(uid.into()),
            cedar_policy_symcc::term::TermPrim::Ext(ext) => Self::Ext(match ext {
                cedar_policy_symcc::ext::Ext::Datetime { dt } => Ext::Datetime {
                    dt: Datetime { val: dt.into() },
                },
                cedar_policy_symcc::ext::Ext::Duration { d } => Ext::Duration {
                    dur: Duration { val: d.into() },
                },
                cedar_policy_symcc::ext::Ext::Decimal { d } => Ext::Decimal { d: Decimal(d.0) },
                cedar_policy_symcc::ext::Ext::Ipaddr { ip } => Ext::Ipaddr {
                    ip: match ip {
                        cedar_policy_symcc::extension_types::ipaddr::IPNet::V4(cidr) => {
                            IpAddr::V4(Cidr {
                                addr: cidr.addr.val.into(),
                                prefix: cidr.prefix.val.map(Into::into),
                            })
                        }
                        cedar_policy_symcc::extension_types::ipaddr::IPNet::V6(cidr) => {
                            IpAddr::V6(Cidr {
                                addr: cidr.addr.val.into(),
                                prefix: cidr.prefix.val.map(Into::into),
                            })
                        }
                    },
                },
            }),
            cedar_policy_symcc::term::TermPrim::String(s) => Self::String(s),
        }
    }
}

impl From<cedar_policy_symcc::op::Uuf> for Uuf {
    fn from(value: cedar_policy_symcc::op::Uuf) -> Self {
        Self {
            id: value.id,
            arg: value.arg.into(),
            out: value.out.into(),
        }
    }
}

impl From<cedar_policy_symcc::op::ExtOp> for ExtOp {
    fn from(value: cedar_policy_symcc::op::ExtOp) -> Self {
        match value {
            cedar_policy_symcc::op::ExtOp::DatetimeOfBitVec => Self::DatetimeOfBitVec,
            cedar_policy_symcc::op::ExtOp::DatetimeVal => Self::DatetimeVal,
            cedar_policy_symcc::op::ExtOp::DecimalVal => Self::DecimalVal,
            cedar_policy_symcc::op::ExtOp::DurationOfBitVec => Self::DurationOfBitVec,
            cedar_policy_symcc::op::ExtOp::DurationVal => Self::DurationVal,
            cedar_policy_symcc::op::ExtOp::IpaddrAddrV4 => Self::IPaddrAddrV4,
            cedar_policy_symcc::op::ExtOp::IpaddrAddrV6 => Self::IPaddrAddrV6,
            cedar_policy_symcc::op::ExtOp::IpaddrIsV4 => Self::IPaddrIsV4,
            cedar_policy_symcc::op::ExtOp::IpaddrPrefixV4 => Self::IPaddrPrefixV4,
            cedar_policy_symcc::op::ExtOp::IpaddrPrefixV6 => Self::IPaddrPrefixV6,
        }
    }
}

impl From<cedar_policy_core::ast::PatternElem> for PatElem {
    fn from(value: cedar_policy_core::ast::PatternElem) -> Self {
        match value {
            cedar_policy_core::ast::PatternElem::Char(c) => Self::Char { c: c.into() },
            cedar_policy_core::ast::PatternElem::Wildcard => Self::Star,
        }
    }
}

impl From<cedar_policy_symcc::op::Op> for Op {
    fn from(value: cedar_policy_symcc::op::Op) -> Self {
        match value {
            cedar_policy_symcc::op::Op::And => Self::And,
            cedar_policy_symcc::op::Op::Or => Self::Or,
            cedar_policy_symcc::op::Op::Not => Self::Not,
            cedar_policy_symcc::op::Op::Eq => Self::Eq,
            cedar_policy_symcc::op::Op::Ite => Self::Ite,
            cedar_policy_symcc::op::Op::Bvadd => Self::Bvadd,
            cedar_policy_symcc::op::Op::Bvsaddo => Self::Bvsaddo,
            cedar_policy_symcc::op::Op::Bvlshr => Self::Bvlshr,
            cedar_policy_symcc::op::Op::Bvmul => Self::Bvmul,
            cedar_policy_symcc::op::Op::Bvneg => Self::Bvneg,
            cedar_policy_symcc::op::Op::Bvnego => Self::Bvnego,
            cedar_policy_symcc::op::Op::Bvsdiv => Self::Bvsdiv,
            cedar_policy_symcc::op::Op::Bvshl => Self::Bvshl,
            cedar_policy_symcc::op::Op::Bvsle => Self::Bvsle,
            cedar_policy_symcc::op::Op::Bvsmod => Self::Bvsmod,
            cedar_policy_symcc::op::Op::Bvslt => Self::Bvslt,
            cedar_policy_symcc::op::Op::Bvsub => Self::Bvsub,
            cedar_policy_symcc::op::Op::Bvsmulo => Self::Bvsmulo,
            cedar_policy_symcc::op::Op::Bvsrem => Self::Bvsrem,
            cedar_policy_symcc::op::Op::Bvssubo => Self::Bvssubo,
            cedar_policy_symcc::op::Op::Bvudiv => Self::Bvudiv,
            cedar_policy_symcc::op::Op::Bvule => Self::Bvule,
            cedar_policy_symcc::op::Op::Bvult => Self::Bvult,
            cedar_policy_symcc::op::Op::Bvumod => Self::Bvumod,
            cedar_policy_symcc::op::Op::Uuf(uuf) => Self::Uuf(Arc::unwrap_or_clone(uuf).into()),
            cedar_policy_symcc::op::Op::OptionGet => Self::OptionGet,
            cedar_policy_symcc::op::Op::RecordGet(a) => Self::RecordGet(a),
            cedar_policy_symcc::op::Op::SetInter => Self::SetInter,
            cedar_policy_symcc::op::Op::SetMember => Self::SetMember,
            cedar_policy_symcc::op::Op::SetSubset => Self::SetSubset,
            cedar_policy_symcc::op::Op::ZeroExtend(u) => Self::ZeroExtend(u.try_into().unwrap()),
            cedar_policy_symcc::op::Op::StringLike(pat) => {
                Self::StringLike(pat.get_elems().iter().map(|p| (*p).into()).collect())
            }
            cedar_policy_symcc::op::Op::Ext(op) => Self::Ext(op.into()),
        }
    }
}

impl From<cedar_policy_symcc::term::TermVar> for TermVar {
    fn from(value: cedar_policy_symcc::term::TermVar) -> Self {
        Self {
            id: value.id,
            ty: value.ty.into(),
        }
    }
}

impl From<cedar_policy_symcc::term::Term> for Term {
    fn from(value: cedar_policy_symcc::term::Term) -> Self {
        match value {
            cedar_policy_symcc::term::Term::App { op, args, ret_ty } => Term::App {
                op: op.into(),
                args: Arc::unwrap_or_clone(args)
                    .into_iter()
                    .map(|t| t.into())
                    .collect(),
                ret_ty: ret_ty.into(),
            },
            cedar_policy_symcc::term::Term::None(ty) => Term::None(ty.into()),
            cedar_policy_symcc::term::Term::Prim(prim) => Term::Prim(prim.into()),
            cedar_policy_symcc::term::Term::Record(r) => Term::Record(
                Arc::unwrap_or_clone(r)
                    .into_iter()
                    .map(|(a, t)| (a, t.into()))
                    .collect(),
            ),
            cedar_policy_symcc::term::Term::Set { elts, elts_ty } => Term::Set {
                elts: Arc::unwrap_or_clone(elts)
                    .into_iter()
                    .map(|t| t.into())
                    .collect(),
                elts_ty: elts_ty.into(),
            },
            cedar_policy_symcc::term::Term::Some(term) => {
                Term::Some(Box::new(Arc::unwrap_or_clone(term).into()))
            }
            cedar_policy_symcc::term::Term::Var(var) => Term::Var(var.into()),
        }
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Prim {
    Bool(bool),
    Int(i64),
    String(String),
    #[serde(rename = "entityUID")]
    EntityUid(EntityUid),
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Value {
    Prim {
        p: Prim,
    },
    Set {
        s: Vec<Value>,
    },
    Record {
        /// Lean gives us a JSON array of pairs, not a JSON object (map)
        m: Vec<(String, Value)>,
    },
    Ext {
        x: Ext,
    },
}

impl TryFrom<Value> for RestrictedExpression {
    type Error = Box<dyn miette::Diagnostic>;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Prim { p: Prim::Bool(b) } => Ok(RestrictedExpression::new_bool(b)),
            Value::Prim { p: Prim::Int(i) } => Ok(RestrictedExpression::new_long(i)),
            Value::Prim { p: Prim::String(s) } => Ok(RestrictedExpression::new_string(s)),
            Value::Prim {
                p: Prim::EntityUid(euid),
            } => Ok(RestrictedExpression::new_entity_uid(euid.into())),
            Value::Set { s } => Ok(RestrictedExpression::new_set(
                s.into_iter()
                    .map(TryInto::try_into)
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Value::Record { m } => Ok(RestrictedExpression::new_record(
                m.into_iter()
                    .map(|(k, v)| Ok((k, v.try_into()?)))
                    .collect::<Result<Vec<_>, Box<dyn miette::Diagnostic>>>()?,
            )?),
            Value::Ext {
                x: Ext::Decimal { d },
            } => Ok(d.into()),
            Value::Ext {
                x: Ext::Ipaddr { ip },
            } => Ok(ip.into()),
            Value::Ext {
                x: Ext::Datetime { dt },
            } => Ok(dt.try_into()?),
            Value::Ext {
                x: Ext::Duration { dur },
            } => Ok(dur.into()),
        }
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Request {
    pub principal: EntityUid,
    pub action: EntityUid,
    pub resource: EntityUid,
    /// Lean gives us a JSON array of pairs, not a JSON object (map)
    pub context: Vec<(String, Value)>,
}

impl TryFrom<Request> for cedar_policy::Request {
    type Error = Box<dyn miette::Diagnostic>;
    fn try_from(req: Request) -> Result<Self, Self::Error> {
        Ok(Self::new(
            req.principal.into(),
            req.action.into(),
            req.resource.into(),
            cedar_policy::Context::from_pairs(
                req.context
                    .into_iter()
                    .map(|(k, v)| Ok((k, v.try_into()?)))
                    .collect::<Result<Vec<_>, Box<dyn miette::Diagnostic>>>()?,
            )?,
            None,
        )?)
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct EntityData {
    /// Lean gives us a JSON array of pairs, not a JSON object (map)
    pub attrs: Vec<(String, Value)>,
    pub ancestors: Vec<EntityUid>,
    /// Lean gives us a JSON array of pairs, not a JSON object (map)
    pub tags: Vec<(String, Value)>,
}

/// Represent a counterexample
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Env {
    /// The request
    pub request: Request,
    /// The entities
    ///
    /// Lean gives us a JSON array of pairs, not a JSON object (map)
    pub entities: Vec<(EntityUid, EntityData)>,
}

impl TryFrom<Env> for cedar_policy_symcc::Env {
    type Error = Box<dyn miette::Diagnostic>;
    fn try_from(env: Env) -> Result<Self, Self::Error> {
        Ok(Self {
            request: env.request.try_into()?,
            entities: cedar_policy::Entities::from_entities(
                env.entities
                    .into_iter()
                    .map(|(uid, ed)| {
                        Ok(cedar_policy::Entity::new_with_tags(
                            uid.into(),
                            ed.attrs
                                .into_iter()
                                .map(|(k, v)| Ok((k, v.try_into()?)))
                                .collect::<Result<Vec<_>, Box<dyn miette::Diagnostic>>>()?,
                            ed.ancestors.into_iter().map(|uid| uid.into()),
                            ed.tags
                                .into_iter()
                                .map(|(k, v)| Ok((k, v.try_into()?)))
                                .collect::<Result<Vec<_>, Box<dyn miette::Diagnostic>>>()?,
                        )?)
                    })
                    .collect::<Result<Vec<_>, Box<dyn miette::Diagnostic>>>()?,
                None,
            )?,
        })
    }
}

#[cfg(test)]
mod deserialization {
    use crate::Bitvec;

    #[test]
    fn bitvec() {
        let json = serde_json::json!(
            {"value": "9223372036854775808", "size": 64});
        let bv: Bitvec = serde_json::from_value(json).expect("deserialization should succeed");
        assert_eq!(bv.width, 64);
        assert_eq!(bv.val, "9223372036854775808");
        let bv =
            cedar_policy_symcc::bitvec::BitVec::try_from(bv).expect("conversion should succeed");
        assert_eq!(bv.width().get(), 64);
        assert_eq!(bv.to_nat().to_string(), "9223372036854775808");
    }

    #[test]
    fn term() {
        let json = serde_json::json!(
                [{"prim": {"bool": true}},
        {"app":
         {"retTy": {"prim": {"pty": "bool"}},
          "op": "not",
          "args":
          [{"app":
            {"retTy": {"prim": {"pty": "bool"}},
             "op": "eq",
             "args":
             [{"var":
               {"ty":
                {"prim": {"pty": {"entity": {"ety": {"path": [], "id": "a"}}}}},
                "id": "resource"}},
              {"prim":
               {"entity": {"ty": {"path": [], "id": "a"}, "eid": ""}}}]}}]}}]
            );
        let _: Vec<crate::Term> =
            serde_json::from_value(json).expect("deserialization should succeed");
    }
}

#[cfg(test)]
mod term_conversion {
    #[test]
    fn roundtrip_pattern() {
        let pattern = cedar_policy_core::ast::PatternElem::Char('a');
        assert_eq!(
            cedar_policy_core::ast::PatternElem::try_from(crate::datatypes::PatElem::from(pattern))
                .unwrap(),
            pattern
        );
    }
}
