use cedar_policy::{Decision, EntityId, EntityTypeName, EntityUid, PolicyId};
use serde::{Deserialize, Deserializer};

use std::collections::HashSet;
use std::str::FromStr;

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
    Char {
        c : u32,
    }
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
    #[serde(deserialize_with = "deserialize_entity_type_name")]
    Entity {
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
    Set {
        elts: Vec<Term>,
        elts_ty: TermType,
    },
    Record(Vec<(String, Term)>),
    App {
        op: Op,
        args: Vec<Term>,
        ret_ty: TermType,
    },
}
