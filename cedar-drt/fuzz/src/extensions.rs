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

//! Inputs and test drivers for fuzz targets that exercise the `decimal`, `ip`,
//! `datetime`, and `duration` extension functions in isolation.
//!
//! There are two kinds of targets:
//! * Constructor targets apply a constructor to an arbitrary string and diff
//!   test the result. These find disagreements on which strings parse and
//!   what they parse to.
//! * The round trip target generates an extension value, renders it as a
//!   string, and checks that the constructor recovers that value. Because the
//!   expected result is computed independently of both implementations, this
//!   also catches bugs shared by the Rust implementation and the Lean model,
//!   such as both rejecting a valid string.

use cedar_drt::tests::run_eval_test;
use cedar_policy::{
    Context, Entities, EntityUid, EvalResult, Expression, Request, eval_expression,
};
use cedar_policy_core::ast::{Expr, Name};
use cedar_testing::cedar_test_impl::CedarTestImplementation;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// An extension type constructor
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtensionConstructor {
    Decimal,
    Ip,
    Datetime,
    Duration,
}

impl ExtensionConstructor {
    fn name(self) -> &'static str {
        match self {
            Self::Decimal => "decimal",
            Self::Ip => "ip",
            Self::Datetime => "datetime",
            Self::Duration => "duration",
        }
    }

    /// Apply this constructor to the string literal `arg`
    fn apply(self, arg: impl Into<String>) -> Expr {
        call(self.name(), vec![Expr::val(arg.into())])
    }
}

/// Call the extension function `name` on `args`
fn call(name: &str, args: Vec<Expr>) -> Expr {
    let name: Name = name
        .parse()
        .expect("extension function names should be valid names");
    Expr::call_extension_fn(name, args)
}

/// Extension functions do not depend on the request, so every test uses the
/// same request.
fn request() -> Request {
    let uid: EntityUid = r#"Test::"""#.parse().expect("entity UID should parse");
    Request::new(uid.clone(), uid.clone(), uid, Context::empty(), None)
        .expect("request without a schema should be valid")
}

/// Diff test the extension constructor `constructor` applied to `arg`, which
/// is usually an arbitrary string.
pub fn run_ext_constructor_test(
    custom_impl: &impl CedarTestImplementation,
    constructor: ExtensionConstructor,
    arg: String,
) {
    run_eval_test(
        custom_impl,
        &request(),
        &constructor.apply(arg).into(),
        &Entities::empty(),
    );
}

/// Check that each expression in `input` evaluates to its expected value in
/// Rust, and diff test the expression against `custom_impl`.
pub fn run_ext_roundtrip_test(
    custom_impl: &impl CedarTestImplementation,
    input: &ExtensionRoundtripInput,
) {
    let request = request();
    let entities = Entities::empty();
    for (expr, expected) in input.checks() {
        let expr = Expression::from(expr);
        let actual = eval_expression(&request, &entities, &expr);
        assert_eq!(
            actual.as_ref().ok(),
            Some(&expected),
            "Unexpected result for {expr}\nActual: {actual:?}\nExpected: {expected:?}",
        );
        run_eval_test(custom_impl, &request, &expr, &entities);
    }
}

/// Input to the extension round trip target: two values of one extension
/// type, where the first is rendered as a string twice, possibly in different
/// but equivalent ways.
#[derive(Debug, Clone)]
pub enum ExtensionRoundtripInput {
    Decimal(RoundtripPair<DecimalValue>),
    Ip(RoundtripPair<IpValue>),
    Datetime(RoundtripPair<DatetimeValue>),
    Duration(RoundtripPair<DurationValue>),
}

impl<'a> Arbitrary<'a> for ExtensionRoundtripInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(match u.int_in_range(0..=3)? {
            0 => Self::Decimal(RoundtripPair::arbitrary(u)?),
            1 => Self::Ip(RoundtripPair::arbitrary(u)?),
            2 => Self::Datetime(RoundtripPair::arbitrary(u)?),
            _ => Self::Duration(RoundtripPair::arbitrary(u)?),
        })
    }
}

impl ExtensionRoundtripInput {
    /// Expressions over the generated values paired with the values they must
    /// evaluate to
    pub fn checks(&self) -> Vec<(Expr, EvalResult)> {
        match self {
            Self::Decimal(pair) => pair.checks(),
            Self::Ip(pair) => pair.checks(),
            Self::Datetime(pair) => pair.checks(),
            Self::Duration(pair) => pair.checks(),
        }
    }
}

/// An extension value that can be generated together with string renderings
/// that denote it
pub trait RoundtripValue: Sized + std::fmt::Debug {
    const CONSTRUCTOR: ExtensionConstructor;

    /// Generate a value
    fn arbitrary_value(u: &mut Unstructured<'_>) -> arbitrary::Result<Self>;

    /// Generate a value that is likely to be close to `self`, so that
    /// comparisons between the two are interesting
    fn arbitrary_neighbor(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<Self>;

    /// Generate a string that the constructor should parse to `self`
    fn arbitrary_rendering(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<String>;

    /// Whether the two values are equal according to Cedar's `==`
    fn cedar_eq(&self, other: &Self) -> bool;

    /// Expressions over `lhs`, which evaluates to `self`, and `rhs`, which
    /// evaluates to `other`, paired with the values they must evaluate to.
    /// Equality is checked separately for all types.
    fn checks(&self, lhs: Expr, other: &Self, rhs: Expr) -> Vec<(Expr, EvalResult)>;
}

/// Two generated values, with two independently generated renderings of the
/// first one
#[derive(Debug, Clone)]
pub struct RoundtripPair<V> {
    lhs: V,
    lhs_str: String,
    lhs_alt_str: String,
    rhs: V,
    rhs_str: String,
}

impl<'a, V: RoundtripValue> Arbitrary<'a> for RoundtripPair<V> {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let lhs = V::arbitrary_value(u)?;
        let lhs_str = lhs.arbitrary_rendering(u)?;
        let lhs_alt_str = lhs.arbitrary_rendering(u)?;
        let rhs = if u.arbitrary()? {
            lhs.arbitrary_neighbor(u)?
        } else {
            V::arbitrary_value(u)?
        };
        let rhs_str = rhs.arbitrary_rendering(u)?;
        Ok(Self {
            lhs,
            lhs_str,
            lhs_alt_str,
            rhs,
            rhs_str,
        })
    }
}

impl<V: RoundtripValue> RoundtripPair<V> {
    fn checks(&self) -> Vec<(Expr, EvalResult)> {
        let lhs = V::CONSTRUCTOR.apply(&self.lhs_str);
        let lhs_alt = V::CONSTRUCTOR.apply(&self.lhs_alt_str);
        let rhs = V::CONSTRUCTOR.apply(&self.rhs_str);
        let mut checks = vec![
            (Expr::is_eq(lhs.clone(), lhs_alt), EvalResult::Bool(true)),
            (
                Expr::is_eq(lhs.clone(), rhs.clone()),
                EvalResult::Bool(self.lhs.cedar_eq(&self.rhs)),
            ),
        ];
        checks.extend(self.lhs.checks(lhs, &self.rhs, rhs));
        checks
    }
}

/// Call the binary extension function `name` on `lhs` and `rhs`
fn call2(name: &str, lhs: &Expr, rhs: &Expr) -> Expr {
    call(name, vec![lhs.clone(), rhs.clone()])
}

/// Call the unary extension function `name` on `arg`
fn call1(name: &str, arg: &Expr) -> Expr {
    call(name, vec![arg.clone()])
}

/// A `decimal` value, stored as its internal representation: the number
/// multiplied by 10^4
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecimalValue(i64);

impl RoundtripValue for DecimalValue {
    const CONSTRUCTOR: ExtensionConstructor = ExtensionConstructor::Decimal;

    fn arbitrary_value(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        Ok(Self(u.arbitrary()?))
    }

    fn arbitrary_neighbor(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        Ok(Self(self.0.saturating_add(u.arbitrary::<i8>()?.into())))
    }

    fn arbitrary_rendering(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<String> {
        let abs = self.0.unsigned_abs();
        let fraction = format!("{:04}", abs % 10_000);
        // Fractional digits needed to represent the value exactly. We always
        // need at least one, and may add trailing zeros up to four digits.
        let needed = fraction.trim_end_matches('0').len().max(1);
        let digits = u.int_in_range(needed..=4)?;
        let sign = if self.0 < 0 { "-" } else { "" };
        Ok(format!("{sign}{}.{}", abs / 10_000, &fraction[..digits]))
    }

    fn cedar_eq(&self, other: &Self) -> bool {
        self == other
    }

    fn checks(&self, lhs: Expr, other: &Self, rhs: Expr) -> Vec<(Expr, EvalResult)> {
        vec![
            (
                call2("lessThan", &lhs, &rhs),
                EvalResult::Bool(self.0 < other.0),
            ),
            (
                call2("lessThanOrEqual", &lhs, &rhs),
                EvalResult::Bool(self.0 <= other.0),
            ),
            (
                call2("greaterThan", &lhs, &rhs),
                EvalResult::Bool(self.0 > other.0),
            ),
            (
                call2("greaterThanOrEqual", &lhs, &rhs),
                EvalResult::Bool(self.0 >= other.0),
            ),
        ]
    }
}

/// A `duration` value, stored as its sign and the quantity of each unit
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DurationValue {
    negative: bool,
    /// Quantities for days, hours, minutes, seconds, and milliseconds.
    /// `None` means that the unit is omitted.
    quantities: [Option<u64>; 5],
}

impl DurationValue {
    /// Unit suffixes from the largest to the smallest unit
    const UNITS: [&str; 5] = ["d", "h", "m", "s", "ms"];
    /// Milliseconds per unit, in the same order as `UNITS`
    const MILLIS: [i64; 5] = [86_400_000, 3_600_000, 60_000, 1_000, 1];
    /// Exclusive upper bound on the quantity for each unit, in the same order
    /// as `UNITS`. These keep the total far from the bounds of `i64`, so no
    /// intermediate result of either implementation overflows.
    const BOUNDS: [u64; 5] = [
        100_000_000,
        1_000_000_000,
        10_000_000_000,
        1_000_000_000_000,
        1_000_000_000_000_000,
    ];

    fn millis(&self) -> i64 {
        let total: i64 = self
            .quantities
            .iter()
            .zip(Self::MILLIS)
            .map(|(q, ms)| i64::try_from(q.unwrap_or(0)).expect("quantity is bounded") * ms)
            .sum();
        if self.negative { -total } else { total }
    }
}

impl RoundtripValue for DurationValue {
    const CONSTRUCTOR: ExtensionConstructor = ExtensionConstructor::Duration;

    fn arbitrary_value(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let negative = u.arbitrary()?;
        let mut quantities = [None; 5];
        for (q, bound) in quantities.iter_mut().zip(Self::BOUNDS) {
            if u.arbitrary()? {
                // Prefer small quantities, which are the common case
                let bound = if u.arbitrary()? { 100 } else { bound };
                *q = Some(u.int_in_range(0..=bound - 1)?);
            }
        }
        // A duration string needs at least one unit
        if quantities.iter().all(Option::is_none) {
            quantities[4] = Some(0);
        }
        Ok(Self {
            negative,
            quantities,
        })
    }

    fn arbitrary_neighbor(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let mut neighbor = self.clone();
        let ms = neighbor.quantities[4].unwrap_or(0);
        neighbor.quantities[4] = Some(ms.saturating_add(u.int_in_range(0..=2)?));
        Ok(neighbor)
    }

    fn arbitrary_rendering(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<String> {
        let mut rendering = if self.negative { "-" } else { "" }.to_string();
        for (q, unit) in self.quantities.iter().zip(Self::UNITS) {
            match q {
                Some(q) => rendering.push_str(&format!("{q}{unit}")),
                // An omitted unit may also be written with quantity zero
                None if u.arbitrary()? => rendering.push_str(&format!("0{unit}")),
                None => {}
            }
        }
        Ok(rendering)
    }

    fn cedar_eq(&self, other: &Self) -> bool {
        self.millis() == other.millis()
    }

    fn checks(&self, lhs: Expr, other: &Self, rhs: Expr) -> Vec<(Expr, EvalResult)> {
        let ms = self.millis();
        vec![
            (
                Expr::is_eq(
                    lhs.clone(),
                    ExtensionConstructor::Duration.apply(format!("{ms}ms")),
                ),
                EvalResult::Bool(true),
            ),
            (call1("toMilliseconds", &lhs), EvalResult::Long(ms)),
            (call1("toSeconds", &lhs), EvalResult::Long(ms / 1_000)),
            (call1("toMinutes", &lhs), EvalResult::Long(ms / 60_000)),
            (call1("toHours", &lhs), EvalResult::Long(ms / 3_600_000)),
            (call1("toDays", &lhs), EvalResult::Long(ms / 86_400_000)),
            (
                Expr::less(lhs.clone(), rhs.clone()),
                EvalResult::Bool(ms < other.millis()),
            ),
            (
                Expr::lesseq(lhs, rhs),
                EvalResult::Bool(ms <= other.millis()),
            ),
        ]
    }
}

/// A `datetime` value, stored as its components
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DatetimeValue {
    year: u16,
    month: u8,
    day: u8,
    /// `None` for a date without a time
    time: Option<TimeOfDay>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TimeOfDay {
    hour: u8,
    minute: u8,
    second: u8,
    /// `None` when the milliseconds are omitted
    millis: Option<u16>,
    /// Offset from UTC in minutes. `None` for UTC written as `Z`.
    offset: Option<i16>,
}

const MILLIS_PER_DAY: i64 = 86_400_000;

/// Number of days from 1970-01-01 to the given date in the proleptic
/// Gregorian calendar. This is the `days_from_civil` algorithm from
/// <https://howardhinnant.github.io/date_algorithms.html>.
fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let year_of_era = year - era * 400;
    let month_from_march = (month + 9) % 12;
    let day_of_year = (153 * month_from_march + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

fn days_in_month(year: u16, month: u8) -> u8 {
    match month {
        2 if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

impl DatetimeValue {
    /// Milliseconds since the Unix epoch
    fn millis(&self) -> i64 {
        let days = days_from_civil(self.year.into(), self.month.into(), self.day.into());
        let time = self.time.as_ref().map_or(0, |t| {
            i64::from(t.hour) * 3_600_000
                + i64::from(t.minute) * 60_000
                + i64::from(t.second) * 1_000
                + i64::from(t.millis.unwrap_or(0))
                - i64::from(t.offset.unwrap_or(0)) * 60_000
        });
        days * MILLIS_PER_DAY + time
    }
}

impl RoundtripValue for DatetimeValue {
    const CONSTRUCTOR: ExtensionConstructor = ExtensionConstructor::Datetime;

    fn arbitrary_value(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let year = u.int_in_range(0..=9999)?;
        let month = u.int_in_range(1..=12)?;
        let day = u.int_in_range(1..=days_in_month(year, month))?;
        let time = if u.arbitrary()? {
            Some(TimeOfDay {
                hour: u.int_in_range(0..=23)?,
                minute: u.int_in_range(0..=59)?,
                second: u.int_in_range(0..=59)?,
                millis: if u.arbitrary()? {
                    Some(u.int_in_range(0..=999)?)
                } else {
                    None
                },
                offset: if u.arbitrary()? {
                    // Offsets range from -23:59 to +23:59
                    Some(u.int_in_range(-(23 * 60 + 59)..=23 * 60 + 59)?)
                } else {
                    None
                },
            })
        } else {
            None
        };
        Ok(Self {
            year,
            month,
            day,
            time,
        })
    }

    fn arbitrary_neighbor(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let mut neighbor = self.clone();
        match &mut neighbor.time {
            Some(time) => {
                time.second = u.int_in_range(0..=59)?;
                time.millis = Some(u.int_in_range(0..=999)?);
            }
            None => neighbor.day = u.int_in_range(1..=days_in_month(self.year, self.month))?,
        }
        Ok(neighbor)
    }

    fn arbitrary_rendering(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<String> {
        let date = format!("{:04}-{:02}-{:02}", self.year, self.month, self.day);
        // A date without a time may also be written as midnight UTC
        let midnight = TimeOfDay {
            hour: 0,
            minute: 0,
            second: 0,
            millis: None,
            offset: None,
        };
        let time = match &self.time {
            None if u.arbitrary()? => return Ok(date),
            None => &midnight,
            Some(time) => time,
        };
        let millis = match time.millis {
            Some(ms) => format!(".{ms:03}"),
            // Omitted milliseconds may also be written as zero
            None if u.arbitrary()? => ".000".to_string(),
            None => String::new(),
        };
        let offset = match time.offset {
            // UTC may also be written as a zero offset
            None => u.choose(&["Z", "+0000", "-0000"])?.to_string(),
            Some(offset) => {
                let sign = if offset < 0 { '-' } else { '+' };
                let offset = offset.unsigned_abs();
                format!("{sign}{:02}{:02}", offset / 60, offset % 60)
            }
        };
        Ok(format!(
            "{date}T{:02}:{:02}:{:02}{millis}{offset}",
            time.hour, time.minute, time.second
        ))
    }

    fn cedar_eq(&self, other: &Self) -> bool {
        self.millis() == other.millis()
    }

    fn checks(&self, lhs: Expr, other: &Self, rhs: Expr) -> Vec<(Expr, EvalResult)> {
        let ms = self.millis();
        let epoch = ExtensionConstructor::Datetime.apply("1970-01-01");
        let since_epoch = |e: Expr| call1("toMilliseconds", &call2("durationSince", &e, &epoch));
        vec![
            (since_epoch(lhs.clone()), EvalResult::Long(ms)),
            (
                since_epoch(call1("toDate", &lhs)),
                EvalResult::Long(ms.div_euclid(MILLIS_PER_DAY) * MILLIS_PER_DAY),
            ),
            (
                call1("toMilliseconds", &call1("toTime", &lhs)),
                EvalResult::Long(ms.rem_euclid(MILLIS_PER_DAY)),
            ),
            (
                Expr::less(lhs.clone(), rhs.clone()),
                EvalResult::Bool(ms < other.millis()),
            ),
            (
                Expr::lesseq(lhs, rhs),
                EvalResult::Bool(ms <= other.millis()),
            ),
        ]
    }
}

/// An `ip` value: an IPv4 or IPv6 address with a prefix length
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IpValue {
    v4: bool,
    /// The address. For IPv4, only the low 32 bits are used.
    addr: u128,
    /// The prefix length, at most `self.width()`
    prefix: u8,
}

impl IpValue {
    fn width(&self) -> u8 {
        if self.v4 { 32 } else { 128 }
    }

    /// The lowest and highest addresses in the range denoted by `self`
    fn range(&self) -> (u128, u128) {
        let host_bits = u32::from(self.width() - self.prefix);
        let host_mask = 1u128.checked_shl(host_bits).map_or(u128::MAX, |b| b - 1);
        (self.addr & !host_mask, self.addr | host_mask)
    }

    fn in_range(&self, other: &Self) -> bool {
        let (lo, hi) = self.range();
        let (other_lo, other_hi) = other.range();
        self.v4 == other.v4 && other_lo <= lo && hi <= other_hi
    }

    fn is_loopback(&self) -> bool {
        let loopback = if self.v4 {
            Self {
                v4: true,
                addr: 0x7f00_0000,
                prefix: 8,
            }
        } else {
            Self {
                v4: false,
                addr: 1,
                prefix: 128,
            }
        };
        self.in_range(&loopback)
    }

    fn is_multicast(&self) -> bool {
        let multicast = if self.v4 {
            Self {
                v4: true,
                addr: 0xe000_0000,
                prefix: 4,
            }
        } else {
            Self {
                v4: false,
                addr: 0xff00 << 112,
                prefix: 8,
            }
        };
        self.in_range(&multicast)
    }
}

impl RoundtripValue for IpValue {
    const CONSTRUCTOR: ExtensionConstructor = ExtensionConstructor::Ip;

    fn arbitrary_value(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let v4: bool = u.arbitrary()?;
        let addr = if v4 {
            // Bias the first octet towards the loopback and multicast ranges
            let first: u32 = match u.int_in_range(0..=2)? {
                0 => 127,
                1 => u.int_in_range(224..=239)?,
                _ => u.arbitrary::<u8>()?.into(),
            };
            u128::from((first << 24) | (u.arbitrary::<u32>()? & 0x00ff_ffff))
        } else {
            // Bias the groups towards zero so that `::` and the loopback
            // address are common, and the first group towards multicast
            let mut addr = 0u128;
            for i in 0..8 {
                let group: u16 = match u.int_in_range(0..=3)? {
                    0 | 1 => 0,
                    2 if i == 0 => 0xff00 | u16::from(u.arbitrary::<u8>()?),
                    2 => 1,
                    _ => u.arbitrary()?,
                };
                addr = (addr << 16) | u128::from(group);
            }
            addr
        };
        let width = if v4 { 32 } else { 128 };
        let prefix = if u.arbitrary()? {
            width
        } else {
            u.int_in_range(0..=width)?
        };
        Ok(Self { v4, addr, prefix })
    }

    fn arbitrary_neighbor(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        // Likely to produce a range that contains or is contained in `self`
        Ok(Self {
            prefix: u.int_in_range(0..=self.width())?,
            ..self.clone()
        })
    }

    fn arbitrary_rendering(&self, u: &mut Unstructured<'_>) -> arbitrary::Result<String> {
        let addr = if self.v4 {
            let [a, b, c, d] = u32::try_from(self.addr)
                .expect("IPv4 addresses fit in 32 bits")
                .to_be_bytes();
            format!("{a}.{b}.{c}.{d}")
        } else {
            let groups: Vec<u16> = (0..8)
                .rev()
                .map(|i| (self.addr >> (16 * i)) as u16)
                .collect();
            let pad = u.arbitrary()?;
            let upper = u.arbitrary()?;
            let fmt = |g: &u16| match (pad, upper) {
                (false, false) => format!("{g:x}"),
                (false, true) => format!("{g:X}"),
                (true, false) => format!("{g:04x}"),
                (true, true) => format!("{g:04X}"),
            };
            // Optionally replace one run of zero groups by `::`
            let zero_runs: Vec<(usize, usize)> = groups
                .iter()
                .enumerate()
                .filter(|(i, g)| **g == 0 && (*i == 0 || groups[i - 1] != 0))
                .map(|(start, _)| {
                    let len = groups[start..].iter().take_while(|g| **g == 0).count();
                    (start, len)
                })
                .collect();
            let compressed = if zero_runs.is_empty() || !u.arbitrary()? {
                None
            } else {
                let (start, run_len) = *u.choose(&zero_runs)?;
                // Compress all or part of the run
                let len = u.int_in_range(1..=run_len)?;
                let start = start + u.int_in_range(0..=run_len - len)?;
                Some((start, len))
            };
            match compressed {
                None => groups.iter().map(fmt).collect::<Vec<_>>().join(":"),
                Some((start, len)) => format!(
                    "{}::{}",
                    groups[..start]
                        .iter()
                        .map(fmt)
                        .collect::<Vec<_>>()
                        .join(":"),
                    groups[start + len..]
                        .iter()
                        .map(fmt)
                        .collect::<Vec<_>>()
                        .join(":")
                ),
            }
        };
        // The prefix may be omitted when it covers the whole address
        if self.prefix == self.width() && u.arbitrary()? {
            Ok(addr)
        } else {
            Ok(format!("{addr}/{}", self.prefix))
        }
    }

    fn cedar_eq(&self, other: &Self) -> bool {
        self == other
    }

    fn checks(&self, lhs: Expr, other: &Self, rhs: Expr) -> Vec<(Expr, EvalResult)> {
        vec![
            (call1("isIpv4", &lhs), EvalResult::Bool(self.v4)),
            (call1("isIpv6", &lhs), EvalResult::Bool(!self.v4)),
            (
                call1("isLoopback", &lhs),
                EvalResult::Bool(self.is_loopback()),
            ),
            (
                call1("isMulticast", &lhs),
                EvalResult::Bool(self.is_multicast()),
            ),
            (
                call2("isInRange", &lhs, &rhs),
                EvalResult::Bool(self.in_range(other)),
            ),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn days_from_civil_matches_known_dates() {
        assert_eq!(days_from_civil(1970, 1, 1), 0);
        assert_eq!(days_from_civil(1969, 12, 31), -1);
        assert_eq!(days_from_civil(2000, 3, 1), 11_017);
        assert_eq!(
            days_from_civil(2024, 10, 15) * MILLIS_PER_DAY,
            1_728_950_400_000
        );
        assert_eq!(days_from_civil(0, 1, 1), -719_528);
    }

    #[test]
    fn datetime_millis_applies_offset() {
        // From the Lean unit tests for `Datetime.parse`
        let value = DatetimeValue {
            year: 2024,
            month: 10,
            day: 15,
            time: Some(TimeOfDay {
                hour: 11,
                minute: 38,
                second: 2,
                millis: Some(101),
                offset: Some(-(11 * 60 + 34)),
            }),
        };
        assert_eq!(value.millis(), 1_729_033_922_101);
    }

    #[test]
    fn ip_ranges() {
        let ip = |v4, addr, prefix| IpValue { v4, addr, prefix };
        assert!(ip(true, 0x7f00_0001, 32).is_loopback());
        assert!(!ip(true, 0x7f00_0001, 7).is_loopback());
        assert!(ip(false, 1, 128).is_loopback());
        assert!(!ip(false, 1, 127).is_loopback());
        assert!(ip(true, 0xe000_0000, 4).is_multicast());
        assert!(ip(false, 0xff01 << 112, 8).is_multicast());
        assert!(ip(true, 0x0a01_0203, 24).in_range(&ip(true, 0x0a00_0000, 8)));
        assert!(!ip(true, 0x0a00_0000, 8).in_range(&ip(true, 0x0a01_0203, 24)));
        assert!(ip(false, 5, 0).in_range(&ip(false, 0, 0)));
        assert!(!ip(true, 0, 0).in_range(&ip(false, 0, 0)));
    }

    /// Check the expected results of the round trip target against the Rust
    /// implementation on inputs generated from pseudorandom bytes
    #[test]
    fn roundtrip_checks_hold_in_rust() {
        let request = request();
        let entities = Entities::empty();
        // xorshift64, so that the test is deterministic without extra dependencies
        let mut state: u64 = 0x2545_f491_4f6c_dd1d;
        let mut bytes = vec![0u8; 256];
        for _ in 0..2_000 {
            for b in bytes.iter_mut() {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                *b = state as u8;
            }
            let input = ExtensionRoundtripInput::arbitrary(&mut Unstructured::new(&bytes))
                .expect("generation should succeed");
            for (expr, expected) in input.checks() {
                let expr = Expression::from(expr);
                let actual = eval_expression(&request, &entities, &expr);
                assert_eq!(
                    actual.as_ref().ok(),
                    Some(&expected),
                    "Unexpected result for {expr}\nInput: {input:?}\nActual: {actual:?}",
                );
            }
        }
    }
}
