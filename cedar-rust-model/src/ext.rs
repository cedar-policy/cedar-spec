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

//! Extension types and functions (`decimal`, `ipaddr`, `datetime`, `duration`):
//! `Cedar/Spec/Ext*.lean`. Values use production's representations, and the
//! parsers follow production's algorithms, with plain matchers in place of its
//! regexes and library parsers (trusted to agree in `verification/ext_trusted.rs`).

#![allow(clippy::all)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

use super::value::{clone_str, Error, List, Prim, Str, Value};


// ---------------------------------------------------------------------------
// Data
// ---------------------------------------------------------------------------

/// An IP address without prefix (production's `std::net::IpAddr`).
#[cfg_attr(feature = "verus", verus_verify)]
pub enum IPAddr {
    V4(u32),
    V6(u128),
}

/// An IP network: an address and a prefix length (production's
/// `extensions::ipaddr::IPAddr`). Well-formed values have a prefix of at most
/// 32 (V4) or 128 (V6) bits; see [`ext_wf`].
#[cfg_attr(feature = "verus", verus_verify)]
pub enum IPNet {
    V4(u32, u8),
    V6(u128, u8),
}

/// An extension value (Lean's `Cedar.Spec.Ext`).
#[cfg_attr(feature = "verus", verus_verify)]
pub enum Ext {
    /// `value / 10^4`
    Decimal(i64),
    IPAddr(IPNet),
    /// Milliseconds since the Unix epoch
    Datetime(i64),
    /// Milliseconds
    Duration(i64),
}

/// The extension functions (Lean's `Cedar.Spec.ExtFun`).
#[cfg_attr(feature = "verus", verus_verify)]
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

// Identity in specs: unfolding the 22-way match would slow down proofs.
#[cfg(feature = "verus")]
verus! {
pub open spec fn clone_extfun_spec(f: &ExtFun) -> ExtFun {
    *f
}
}

#[cfg_attr(feature = "verus", verus_verify, verifier::when_used_as_spec(clone_extfun_spec))]
#[cfg_attr(feature = "verus", verus_spec(r => returns clone_extfun_spec(f)))]
pub fn clone_extfun(f: &ExtFun) -> ExtFun {
    match f {
        ExtFun::Decimal => ExtFun::Decimal,
        ExtFun::LessThan => ExtFun::LessThan,
        ExtFun::LessThanOrEqual => ExtFun::LessThanOrEqual,
        ExtFun::GreaterThan => ExtFun::GreaterThan,
        ExtFun::GreaterThanOrEqual => ExtFun::GreaterThanOrEqual,
        ExtFun::Ip => ExtFun::Ip,
        ExtFun::IsIpv4 => ExtFun::IsIpv4,
        ExtFun::IsIpv6 => ExtFun::IsIpv6,
        ExtFun::IsLoopback => ExtFun::IsLoopback,
        ExtFun::IsMulticast => ExtFun::IsMulticast,
        ExtFun::IsInRange => ExtFun::IsInRange,
        ExtFun::Datetime => ExtFun::Datetime,
        ExtFun::Duration => ExtFun::Duration,
        ExtFun::Offset => ExtFun::Offset,
        ExtFun::DurationSince => ExtFun::DurationSince,
        ExtFun::ToDate => ExtFun::ToDate,
        ExtFun::ToTime => ExtFun::ToTime,
        ExtFun::ToMilliseconds => ExtFun::ToMilliseconds,
        ExtFun::ToSeconds => ExtFun::ToSeconds,
        ExtFun::ToMinutes => ExtFun::ToMinutes,
        ExtFun::ToHours => ExtFun::ToHours,
        ExtFun::ToDays => ExtFun::ToDays,
    }
}

/// The result of an extension function.
#[cfg_attr(feature = "verus", verus_verify)]
pub enum ExtRes {
    Bool(bool),
    Int(i64),
    Ext(Ext),
}

/// The components of a duration string matched by production's
/// `DURATION_PATTERN` (the digits of each unit, if present).
#[cfg_attr(feature = "verus", verus_verify)]
pub struct DurParts {
    pub d: Option<Str>,
    pub h: Option<Str>,
    pub m: Option<Str>,
    pub s: Option<Str>,
    pub ms: Option<Str>,
}

// ---------------------------------------------------------------------------
// Truncating division and remainder (Verus's spec `/` and `%` are Euclidean)
// ---------------------------------------------------------------------------

#[cfg(feature = "verus")]
verus! {
/// `x / k`, truncating, for `k > 0`
pub open spec fn tdiv_spec(x: i64, k: i64) -> i64 {
    if x >= 0 { (x as int / k as int) as i64 } else { (-((-(x as int)) / k as int)) as i64 }
}

/// `x % k`, with the sign of `x`, for `k > 0`
pub open spec fn tmod_spec(x: i64, k: i64) -> i64 {
    if x >= 0 { (x as int % k as int) as i64 } else { (-((-(x as int)) % k as int)) as i64 }
}
}

/// `x / k` (truncating), for `k > 0`
#[cfg_attr(feature = "verus", verus_verify, verifier::when_used_as_spec(tdiv_spec))]
#[cfg_attr(feature = "verus", verus_spec(r => requires k > 0, returns tdiv_spec(x, k)))]
pub fn tdiv(x: i64, k: i64) -> i64 {
    x / k
}

/// `x % k` (with the sign of `x`), for `k > 0`
#[cfg_attr(feature = "verus", verus_verify, verifier::when_used_as_spec(tmod_spec))]
#[cfg_attr(feature = "verus", verus_spec(r => requires k > 0, returns tmod_spec(x, k)))]
pub fn tmod(x: i64, k: i64) -> i64 {
    x % k
}

// ---------------------------------------------------------------------------
// Characters and strings
// ---------------------------------------------------------------------------

/// The code point of `c`. Opaque to Aeneas, which can't cast `char`s;
/// hand-written in `lean/CedarRustModel/FunsExternal.lean`.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns char_code(c)))]
pub fn char_code(c: char) -> u32 {
    c as u32
}

/// The value of an ASCII decimal digit
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns digit_val(c)))]
pub fn digit_val(c: char) -> Option<u32> {
    let n = char_code(c);
    if 48 <= n && n <= 57 {
        Some(n - 48)
    } else {
        None
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns is_digit(c)))]
pub fn is_digit(c: char) -> bool {
    match digit_val(c) {
        Some(_) => true,
        None => false,
    }
}

/// The value of an ASCII hexadecimal digit (either case)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns hex_val(c)))]
pub fn hex_val(c: char) -> Option<u32> {
    let n = char_code(c);
    if 48 <= n && n <= 57 {
        Some(n - 48)
    } else if 97 <= n && n <= 102 {
        Some(n - 87)
    } else if 65 <= n && n <= 70 {
        Some(n - 55)
    } else {
        None
    }
}

/// The number of bytes of the UTF-8 encoding of `c`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns utf8_width(c)))]
pub fn utf8_width(c: char) -> u32 {
    let n = char_code(c);
    if n < 0x80 {
        1
    } else if n < 0x800 {
        2
    } else if n < 0x10000 {
        3
    } else {
        4
    }
}

/// Is the UTF-8 encoding of `s` at most `n` bytes long (production's `str::len`)?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns utf8_len_le(s, n)))]
pub fn utf8_len_le(s: &Str, n: u32) -> bool {
    decreases!(s);
    match s {
        List::Nil => true,
        List::Cons(c, rest) => {
            let k = utf8_width(*c);
            if k <= n {
                utf8_len_le(rest, n - k)
            } else {
                false
            }
        }
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns is_empty(s)))]
pub fn is_empty(s: &Str) -> bool {
    match s {
        List::Nil => true,
        List::Cons(_, _) => false,
    }
}

/// Does `s` start with the character `c`?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns starts_with(s, c)))]
pub fn starts_with(s: &Str, c: char) -> bool {
    match s {
        List::Nil => false,
        List::Cons(d, _) => *d == c,
    }
}

/// Is `s` the string consisting of `c` only?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns is_char(s, c)))]
pub fn is_char(s: &Str, c: char) -> bool {
    match s {
        List::Cons(d, rest) => *d == c && is_empty(rest),
        List::Nil => false,
    }
}

/// Does `s` have at most `n` elements?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns len_le(s, n)))]
pub fn len_le<T>(s: &List<T>, n: u32) -> bool {
    decreases!(s);
    match s {
        List::Nil => true,
        List::Cons(_, rest) => {
            if n == 0 {
                false
            } else {
                len_le(rest, n - 1)
            }
        }
    }
}

/// Does `c` occur in `s`?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns has_one(s, c)))]
pub fn has_one(s: &Str, c: char) -> bool {
    decreases!(s);
    match s {
        List::Nil => false,
        List::Cons(d, rest) => *d == c || has_one(rest, c),
    }
}

/// Does `c` occur at least twice in `s`?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns has_two(s, c)))]
pub fn has_two(s: &Str, c: char) -> bool {
    decreases!(s);
    match s {
        List::Nil => false,
        List::Cons(d, rest) => {
            if *d == c {
                has_one(rest, c)
            } else {
                has_two(rest, c)
            }
        }
    }
}

/// Is every character of `s` an ASCII digit? (True for the empty string.)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns all_digits(s)))]
pub fn all_digits(s: &Str) -> bool {
    decreases!(s);
    match s {
        List::Nil => true,
        List::Cons(c, rest) => is_digit(*c) && all_digits(rest),
    }
}

/// `[0-9]+`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns is_digits(s)))]
pub fn is_digits(s: &Str) -> bool {
    !is_empty(s) && all_digits(s)
}

/// `s` split at the first occurrence of `c`, which is dropped
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns split_at_char(s, c)))]
pub fn split_at_char(s: &Str, c: char) -> Option<(Str, Str)> {
    decreases!(s);
    match s {
        List::Nil => None,
        List::Cons(d, rest) => {
            if *d == c {
                Some((List::Nil, clone_str(rest)))
            } else {
                match split_at_char(rest, c) {
                    Some((l, r)) => Some((List::Cons(*d, Box::new(l)), r)),
                    None => None,
                }
            }
        }
    }
}

/// `s` split at every occurrence of `c` (Lean's `String.splitToList (· = c)`).
/// There is always at least one part.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns split_all(s, c)))]
pub fn split_all(s: &Str, c: char) -> List<Str> {
    decreases!(s);
    match s {
        List::Nil => List::Cons(List::Nil, Box::new(List::Nil)),
        List::Cons(d, rest) => {
            let parts = split_all(rest, c);
            if *d == c {
                List::Cons(List::Nil, Box::new(parts))
            } else {
                match parts {
                    List::Cons(p, ps) => List::Cons(List::Cons(*d, Box::new(p)), ps),
                    List::Nil => List::Cons(List::Cons(*d, Box::new(List::Nil)), Box::new(List::Nil)),
                }
            }
        }
    }
}

/// The longest prefix of `s` consisting of ASCII digits, and the rest
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns span_digits(s)))]
pub fn span_digits(s: &Str) -> (Str, Str) {
    decreases!(s);
    match s {
        List::Nil => (List::Nil, List::Nil),
        List::Cons(c, rest) => {
            if is_digit(*c) {
                let (ds, r) = span_digits(rest);
                (List::Cons(*c, Box::new(ds)), r)
            } else {
                (List::Nil, List::Cons(*c, Box::new(clone_str(rest))))
            }
        }
    }
}

/// `s` without its first `n` characters, if they are ASCII digits; the
/// digits and the rest
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns take_digits(s, n)))]
pub fn take_digits(s: &Str, n: u32) -> Option<(Str, Str)> {
    decreases!(s);
    if n == 0 {
        Some((List::Nil, clone_str(s)))
    } else {
        match s {
            List::Nil => None,
            List::Cons(c, rest) => {
                if is_digit(*c) {
                    match take_digits(rest, n - 1) {
                        Some((ds, r)) => Some((List::Cons(*c, Box::new(ds)), r)),
                        None => None,
                    }
                } else {
                    None
                }
            }
        }
    }
}

/// `s` without its first character, if it is `c`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns take_char(s, c)))]
pub fn take_char(s: &Str, c: char) -> Option<Str> {
    match s {
        List::Cons(d, rest) => {
            if *d == c {
                Some(clone_str(rest))
            } else {
                None
            }
        }
        List::Nil => None,
    }
}

// ---------------------------------------------------------------------------
// Integer parsing (`FromStr` for the integer types)
// ---------------------------------------------------------------------------

/// Accumulates the ASCII digits `s` onto `acc`, from left to right, in `i64`:
/// `acc * 10 - d` if `neg`, `acc * 10 + d` otherwise. `None` on overflow or a
/// character that is not a digit.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns digits_i64(s, neg, acc)))]
pub fn digits_i64(s: &Str, neg: bool, acc: i64) -> Option<i64> {
    decreases!(s);
    match s {
        List::Nil => Some(acc),
        List::Cons(c, rest) => match digit_val(*c) {
            None => None,
            Some(d) => match acc.checked_mul(10) {
                None => None,
                Some(a) => {
                    let next = if neg {
                        a.checked_sub(d as i64)
                    } else {
                        a.checked_add(d as i64)
                    };
                    match next {
                        None => None,
                        Some(a2) => digits_i64(rest, neg, a2),
                    }
                }
            },
        },
    }
}

/// `i64::from_str`: an optional sign followed by one or more ASCII digits,
/// in range
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_i64(s)))]
pub fn parse_i64(s: &Str) -> Option<i64> {
    match s {
        List::Nil => None,
        List::Cons(c, rest) => {
            if *c == '-' || *c == '+' {
                if is_empty(rest) {
                    None
                } else {
                    digits_i64(rest, *c == '-', 0)
                }
            } else {
                digits_i64(s, false, 0)
            }
        }
    }
}

/// Accumulates the ASCII digits `s` onto `acc` in `u64`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns digits_u64(s, acc)))]
pub fn digits_u64(s: &Str, acc: u64) -> Option<u64> {
    decreases!(s);
    match s {
        List::Nil => Some(acc),
        List::Cons(c, rest) => match digit_val(*c) {
            None => None,
            Some(d) => match acc.checked_mul(10) {
                None => None,
                Some(a) => match a.checked_add(d as u64) {
                    None => None,
                    Some(a2) => digits_u64(rest, a2),
                },
            },
        },
    }
}

/// `u64::from_str`: an optional `+` followed by one or more ASCII digits, in
/// range
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_u64(s)))]
pub fn parse_u64(s: &Str) -> Option<u64> {
    match s {
        List::Nil => None,
        List::Cons(c, rest) => {
            if *c == '+' {
                if is_empty(rest) {
                    None
                } else {
                    digits_u64(rest, 0)
                }
            } else {
                digits_u64(s, 0)
            }
        }
    }
}

/// `u8::from_str`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_u8(s)))]
pub fn parse_u8(s: &Str) -> Option<u8> {
    match parse_u64(s) {
        Some(n) => {
            if n <= 255 {
                Some(n as u8)
            } else {
                None
            }
        }
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Decimal
// ---------------------------------------------------------------------------

/// `-?[0-9]+`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns is_signed_digits(s)))]
pub fn is_signed_digits(s: &Str) -> bool {
    match s {
        List::Cons(c, rest) => {
            if *c == '-' {
                is_digits(rest)
            } else {
                is_digits(s)
            }
        }
        List::Nil => false,
    }
}

/// Production's `DECIMAL_REGEX` (`^(-?\d+)\.(\d+)$`) with ASCII `\d` (non-ASCII
/// digits are rejected later by `i64::from_str` anyway)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns decimal_split(s)))]
pub fn decimal_split(s: &Str) -> Option<(Str, Str)> {
    match split_at_char(s, '.') {
        Some((l, r)) => {
            if is_signed_digits(&l) && is_digits(&r) {
                Some((l, r))
            } else {
                None
            }
        }
        None => None,
    }
}

/// `10^(4 - len)` for a fractional part of `len` digits, if `1 <= len <= 4`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns frac_scale(r)))]
pub fn frac_scale(r: &Str) -> Option<i64> {
    match r {
        List::Nil => None,
        List::Cons(_, r1) => match &**r1 {
            List::Nil => Some(1000),
            List::Cons(_, r2) => match &**r2 {
                List::Nil => Some(100),
                List::Cons(_, r3) => match &**r3 {
                    List::Nil => Some(10),
                    List::Cons(_, r4) => match &**r4 {
                        List::Nil => Some(1),
                        List::Cons(_, _) => None,
                    },
                },
            },
        },
    }
}

/// Production's `Decimal::from_str` (Lean's `Decimal.parse`)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_decimal(s)))]
pub fn parse_decimal(s: &Str) -> Option<i64> {
    match decimal_split(s) {
        None => None,
        Some((l, r)) => match parse_i64(&l) {
            None => None,
            Some(lv) => match lv.checked_mul(10000) {
                None => None,
                Some(l4) => match frac_scale(&r) {
                    None => None,
                    Some(k) => match parse_i64(&r) {
                        None => None,
                        Some(rv) => match rv.checked_mul(k) {
                            None => None,
                            Some(r4) => {
                                if starts_with(&l, '-') {
                                    l4.checked_sub(r4)
                                } else {
                                    l4.checked_add(r4)
                                }
                            }
                        },
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// IP addresses
// ---------------------------------------------------------------------------

/// A decimal octet of an IPv4 address: 1 to 3 digits, no leading zero, at
/// most 255
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_v4_octet(s)))]
pub fn parse_v4_octet(s: &Str) -> Option<u32> {
    if is_digits(s) && len_le(s, 3) && !(starts_with(s, '0') && !is_char(s, '0')) {
        match digits_u64(s, 0) {
            Some(n) => {
                if n <= 255 {
                    Some(n as u32)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        None
    }
}

/// The IPv4 address with the octets `a0.a1.a2.a3`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns v4_of_octets(a0, a1, a2, a3)))]
pub fn v4_of_octets(a0: u32, a1: u32, a2: u32, a3: u32) -> u32 {
    (a0 << 24) | (a1 << 16) | (a2 << 8) | a3
}

/// The IPv4 address with the octets `g0.g1.g2.g3`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_v4_octets(g0, g1, g2, g3)))]
pub fn parse_v4_octets(g0: &Str, g1: &Str, g2: &Str, g3: &Str) -> Option<u32> {
    match parse_v4_octet(g0) {
        None => None,
        Some(a0) => match parse_v4_octet(g1) {
            None => None,
            Some(a1) => match parse_v4_octet(g2) {
                None => None,
                Some(a2) => match parse_v4_octet(g3) {
                    None => None,
                    Some(a3) => Some(v4_of_octets(a0, a1, a2, a3)),
                },
            },
        },
    }
}

/// An IPv4 address `a.b.c.d`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_v4(s)))]
pub fn parse_v4(s: &Str) -> Option<u32> {
    let parts = split_all(s, '.');
    match &parts {
        List::Cons(g0, r0) => match &**r0 {
            List::Cons(g1, r1) => match &**r1 {
                List::Cons(g2, r2) => match &**r2 {
                    List::Cons(g3, r3) => match &**r3 {
                        List::Nil => parse_v4_octets(g0, g1, g2, g3),
                        List::Cons(_, _) => None,
                    },
                    List::Nil => None,
                },
                List::Nil => None,
            },
            List::Nil => None,
        },
        List::Nil => None,
    }
}

/// Accumulates hexadecimal digits onto `acc` (at most 4 digits: no overflow)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns hex_digits(s, acc)))]
pub fn hex_digits(s: &Str, acc: u32) -> Option<u32> {
    decreases!(s);
    match s {
        List::Nil => Some(acc),
        List::Cons(c, rest) => match hex_val(*c) {
            None => None,
            Some(d) => {
                if acc < 0x1000 {
                    hex_digits(rest, acc * 16 + d)
                } else {
                    None
                }
            }
        },
    }
}

/// A group of an IPv6 address: 1 to 4 hexadecimal digits
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_v6_group(s)))]
pub fn parse_v6_group(s: &Str) -> Option<u32> {
    if !is_empty(s) && len_le(s, 4) {
        hex_digits(s, 0)
    } else {
        None
    }
}

/// The groups of `s` (separated by `:`), all of which must be valid
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_v6_groups_list(gs)))]
pub fn parse_v6_groups_list(gs: &List<Str>) -> Option<List<u32>> {
    decreases!(gs);
    match gs {
        List::Nil => Some(List::Nil),
        List::Cons(g, rest) => match parse_v6_group(g) {
            None => None,
            Some(n) => match parse_v6_groups_list(rest) {
                None => None,
                Some(ns) => Some(List::Cons(n, Box::new(ns))),
            },
        },
    }
}

/// The groups of one side of `::` (none if the side is empty)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_v6_groups(s)))]
pub fn parse_v6_groups(s: &Str) -> Option<List<u32>> {
    if is_empty(s) {
        Some(List::Nil)
    } else {
        parse_v6_groups_list(&split_all(s, ':'))
    }
}

/// `s` split at the first occurrence of `::`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns split_double_colon(s)))]
pub fn split_double_colon(s: &Str) -> Option<(Str, Str)> {
    decreases!(s);
    match s {
        List::Nil => None,
        List::Cons(c, rest) => {
            if *c == ':' && starts_with(rest, ':') {
                match &**rest {
                    List::Cons(_, rest2) => Some((List::Nil, clone_str(rest2))),
                    List::Nil => None,
                }
            } else {
                match split_double_colon(rest) {
                    Some((l, r)) => Some((List::Cons(*c, Box::new(l)), r)),
                    None => None,
                }
            }
        }
    }
}

/// `n` minus the length of `l`, if that is not negative
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns sub_len(l, n)))]
pub fn sub_len(l: &List<u32>, n: u32) -> Option<u32> {
    decreases!(l);
    match l {
        List::Nil => Some(n),
        List::Cons(_, rest) => {
            if n == 0 {
                None
            } else {
                sub_len(rest, n - 1)
            }
        }
    }
}

/// `n` zeros followed by `tail`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns zeros_then(n, tail)))]
pub fn zeros_then(n: u32, tail: List<u32>) -> List<u32> {
    decreases!(n);
    if n == 0 {
        tail
    } else {
        List::Cons(0, Box::new(zeros_then(n - 1, tail)))
    }
}

/// `l` followed by `tail`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns append_u32(l, tail)))]
pub fn append_u32(l: &List<u32>, tail: List<u32>) -> List<u32> {
    decreases!(l);
    match l {
        List::Nil => tail,
        List::Cons(x, rest) => List::Cons(*x, Box::new(append_u32(rest, tail))),
    }
}

/// The IPv6 address with the groups `a0:...:a7`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns v6_of_hextets(a0, a1, a2, a3, a4, a5, a6, a7)))]
pub fn v6_of_hextets(a0: u32, a1: u32, a2: u32, a3: u32, a4: u32, a5: u32, a6: u32, a7: u32) -> u128 {
    ((a0 as u128) << 112)
        | ((a1 as u128) << 96)
        | ((a2 as u128) << 80)
        | ((a3 as u128) << 64)
        | ((a4 as u128) << 48)
        | ((a5 as u128) << 32)
        | ((a6 as u128) << 16)
        | (a7 as u128)
}

/// The address with the 8 groups `gs`, most significant first
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns v6_of_groups(gs)))]
pub fn v6_of_groups(gs: &List<u32>) -> Option<u128> {
    match gs {
        List::Cons(a0, r0) => match &**r0 {
            List::Cons(a1, r1) => match &**r1 {
                List::Cons(a2, r2) => match &**r2 {
                    List::Cons(a3, r3) => match &**r3 {
                        List::Cons(a4, r4) => match &**r4 {
                            List::Cons(a5, r5) => match &**r5 {
                                List::Cons(a6, r6) => match &**r6 {
                                    List::Cons(a7, r7) => match &**r7 {
                                        List::Nil => Some(v6_of_hextets(
                                            *a0, *a1, *a2, *a3, *a4, *a5, *a6, *a7,
                                        )),
                                        List::Cons(_, _) => None,
                                    },
                                    List::Nil => None,
                                },
                                List::Nil => None,
                            },
                            List::Nil => None,
                        },
                        List::Nil => None,
                    },
                    List::Nil => None,
                },
                List::Nil => None,
            },
            List::Nil => None,
        },
        List::Nil => None,
    }
}

/// An IPv6 address, in the RFC 4291 text form with at most one `::` and
/// without an embedded IPv4 address
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_v6(s)))]
pub fn parse_v6(s: &Str) -> Option<u128> {
    match split_double_colon(s) {
        None => match parse_v6_groups(s) {
            Some(gs) => v6_of_groups(&gs),
            None => None,
        },
        Some((l, r)) => match (parse_v6_groups(&l), parse_v6_groups(&r)) {
            (Some(gl), Some(gr)) => match sub_len(&gl, 8) {
                Some(k) => match sub_len(&gr, k) {
                    Some(z) => {
                        if z == 0 {
                            None
                        } else {
                            v6_of_groups(&append_u32(&gl, zeros_then(z, gr)))
                        }
                    }
                    None => None,
                },
                None => None,
            },
            _ => None,
        },
    }
}

/// `std::net::IpAddr::from_str`, on strings without an embedded IPv4 address
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_ip_addr(s)))]
pub fn parse_ip_addr(s: &Str) -> Option<IPAddr> {
    match parse_v4(s) {
        Some(a) => Some(IPAddr::V4(a)),
        None => match parse_v6(s) {
            Some(a) => Some(IPAddr::V6(a)),
            None => None,
        },
    }
}

/// Production's `parse_prefix`: at most `max_len` bytes, ASCII digits, no
/// leading zero, at most `max`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_prefix(s, max, max_len)))]
pub fn parse_prefix(s: &Str, max: u8, max_len: u32) -> Option<u8> {
    if !utf8_len_le(s, max_len) {
        None
    } else if !all_digits(s) {
        None
    } else if starts_with(s, '0') && !is_char(s, '0') {
        None
    } else {
        match parse_u8(s) {
            Some(n) => {
                if n > max {
                    None
                } else {
                    Some(n)
                }
            }
            None => None,
        }
    }
}

/// Production's `IPAddr::from_str` (Lean's `IPAddr.ip`)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_ip(s)))]
pub fn parse_ip(s: &Str) -> Option<IPNet> {
    if !utf8_len_le(s, 43) {
        None
    } else if has_two(s, ':') && has_two(s, '.') {
        None
    } else {
        match split_at_char(s, '/') {
            Some((a, p)) => match parse_ip_addr(&a) {
                Some(IPAddr::V4(x)) => match parse_prefix(&p, 32, 2) {
                    Some(n) => Some(IPNet::V4(x, n)),
                    None => None,
                },
                Some(IPAddr::V6(x)) => match parse_prefix(&p, 128, 3) {
                    Some(n) => Some(IPNet::V6(x, n)),
                    None => None,
                },
                None => None,
            },
            None => match parse_ip_addr(s) {
                Some(IPAddr::V4(x)) => Some(IPNet::V4(x, 32)),
                Some(IPAddr::V6(x)) => Some(IPNet::V6(x, 128)),
                None => None,
            },
        }
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ip_is_v4(ip)))]
pub fn ip_is_v4(ip: &IPNet) -> bool {
    match ip {
        IPNet::V4(_, _) => true,
        IPNet::V6(_, _) => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ip_is_v6(ip)))]
pub fn ip_is_v6(ip: &IPNet) -> bool {
    match ip {
        IPNet::V4(_, _) => false,
        IPNet::V6(_, _) => true,
    }
}

/// Production's `IPAddr::is_loopback`: `127.0.0.0/8` and `::1/128`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ip_is_loopback(ip)))]
pub fn ip_is_loopback(ip: &IPNet) -> bool {
    match ip {
        IPNet::V4(a, p) => (*a >> 24) == 127 && *p >= 8,
        IPNet::V6(a, p) => *a == 1 && *p >= 128,
    }
}

/// Production's `IPAddr::is_multicast`: `224.0.0.0/4` and `ff00::/8`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ip_is_multicast(ip)))]
pub fn ip_is_multicast(ip: &IPNet) -> bool {
    match ip {
        IPNet::V4(a, p) => (*a >> 28) == 14 && *p >= 4,
        IPNet::V6(a, p) => (*a >> 120) == 255 && *p >= 8,
    }
}

/// `u32::MAX.checked_shl(32 - p).unwrap_or(0)`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns v4_netmask(p)))]
pub fn v4_netmask(p: u8) -> u32 {
    if p == 0 {
        0
    } else if p > 32 {
        0xffff_ffff
    } else {
        0xffff_ffffu32 << (32 - p)
    }
}

/// `u32::MAX.checked_shr(p).unwrap_or(0)`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns v4_hostmask(p)))]
pub fn v4_hostmask(p: u8) -> u32 {
    if p >= 32 {
        0
    } else {
        0xffff_ffffu32 >> p
    }
}

/// `u128::MAX.checked_shl(128 - p).unwrap_or(0)`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns v6_netmask(p)))]
pub fn v6_netmask(p: u8) -> u128 {
    if p == 0 {
        0
    } else if p > 128 {
        0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
    } else {
        0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 << (128 - p)
    }
}

/// `u128::MAX.checked_shr(p).unwrap_or(0)`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns v6_hostmask(p)))]
pub fn v6_hostmask(p: u8) -> u128 {
    if p >= 128 {
        0
    } else {
        0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 >> p
    }
}

/// Production's `IPAddr::is_in_range`: is `a`'s range within `b`'s? The masks
/// clip over-long prefixes to the full width, as in Lean.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ip_in_range(a, b)))]
pub fn ip_in_range(a: &IPNet, b: &IPNet) -> bool {
    match (a, b) {
        (IPNet::V4(x, p), IPNet::V4(y, q)) => {
            (*y & v4_netmask(*q)) <= (*x & v4_netmask(*p))
                && (*x | v4_hostmask(*p)) <= (*y | v4_hostmask(*q))
        }
        (IPNet::V6(x, p), IPNet::V6(y, q)) => {
            (*y & v6_netmask(*q)) <= (*x & v6_netmask(*p))
                && (*x | v6_hostmask(*p)) <= (*y | v6_hostmask(*q))
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Datetime and duration
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "verus", verus_verify)]
pub const MS_PER_DAY: i64 = 86_400_000;

/// `^([0-9]{4})-([0-9]{2})-([0-9]{2})`: year, month, day, and the rest
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns match_date(s)))]
pub fn match_date(s: &Str) -> Option<(Str, Str, Str, Str)> {
    match take_digits(s, 4) {
        None => None,
        Some((y, r1)) => match take_char(&r1, '-') {
            None => None,
            Some(r2) => match take_digits(&r2, 2) {
                None => None,
                Some((m, r3)) => match take_char(&r3, '-') {
                    None => None,
                    Some(r4) => match take_digits(&r4, 2) {
                        None => None,
                        Some((d, r5)) => Some((y, m, d, r5)),
                    },
                },
            },
        },
    }
}

/// `^T([0-9]{2}):([0-9]{2}):([0-9]{2})`: hours, minutes, seconds, and the rest
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns match_hms(s)))]
pub fn match_hms(s: &Str) -> Option<(Str, Str, Str, Str)> {
    match take_char(s, 'T') {
        None => None,
        Some(r0) => match take_digits(&r0, 2) {
            None => None,
            Some((h, r1)) => match take_char(&r1, ':') {
                None => None,
                Some(r2) => match take_digits(&r2, 2) {
                    None => None,
                    Some((m, r3)) => match take_char(&r3, ':') {
                        None => None,
                        Some(r4) => match take_digits(&r4, 2) {
                            None => None,
                            Some((sec, r5)) => Some((h, m, sec, r5)),
                        },
                    },
                },
            },
        },
    }
}

/// `^(Z|((\+|-)([0-9]{2})([0-9]{2})))$`: `None` for `Z`, or the offset
/// (whether it is positive, its hours and its minutes)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns match_offset(s)))]
pub fn match_offset(s: &Str) -> Option<Option<(bool, Str, Str)>> {
    match s {
        List::Nil => None,
        List::Cons(c, rest) => {
            if *c == 'Z' {
                if is_empty(rest) {
                    Some(None)
                } else {
                    None
                }
            } else if *c == '+' || *c == '-' {
                match take_digits(rest, 2) {
                    None => None,
                    Some((hh, r1)) => match take_digits(&r1, 2) {
                        None => None,
                        Some((mm, r2)) => {
                            if is_empty(&r2) {
                                Some(Some((*c == '+', hh, mm)))
                            } else {
                                None
                            }
                        }
                    },
                }
            } else {
                None
            }
        }
    }
}

/// `^(\.([0-9]{3}))?(Z|((\+|-)([0-9]{2})([0-9]{2})))$`: the milliseconds (if
/// present) and the offset
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns match_ms_offset(s)))]
pub fn match_ms_offset(s: &Str) -> Option<(Option<Str>, Option<(bool, Str, Str)>)> {
    match take_char(s, '.') {
        Some(r0) => match take_digits(&r0, 3) {
            None => None,
            Some((ms, r1)) => match match_offset(&r1) {
                None => None,
                Some(off) => Some((Some(ms), off)),
            },
        },
        None => match match_offset(s) {
            None => None,
            Some(off) => Some((None, off)),
        },
    }
}

/// The value of a string of (at most 4) ASCII digits
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns small_nat(s)))]
pub fn small_nat(s: &Str) -> i64 {
    match digits_u64(s, 0) {
        Some(n) => {
            if n <= 9999 {
                n as i64
            } else {
                0
            }
        }
        None => 0,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns is_leap_year(y)))]
pub fn is_leap_year(y: i64) -> bool {
    tmod(y, 4) == 0 && (tmod(y, 100) != 0 || tmod(y, 400) == 0)
}

/// The number of days of the month `m` of the year `y` (for `1 <= m <= 12`)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns days_in_month(y, m)))]
pub fn days_in_month(y: i64, m: i64) -> i64 {
    if m == 4 || m == 6 || m == 9 || m == 11 {
        30
    } else if m == 2 {
        if is_leap_year(y) {
            29
        } else {
            28
        }
    } else {
        31
    }
}

/// Is `y-m-d` a valid date (`chrono::NaiveDate::from_ymd_opt` succeeds), for
/// `0 <= y <= 9999`?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns valid_date(y, m, d)))]
pub fn valid_date(y: i64, m: i64, d: i64) -> bool {
    1 <= m && m <= 12 && 1 <= d && d <= days_in_month(y, m)
}

/// Days from 1970-01-01 to a valid `y-m-d`, `0 <= y <= 9999` (Lean's `epochDays`,
/// Howard Hinnant's `days_from_civil`)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 0 <= y <= 9999, 1 <= m <= 12, 1 <= d <= 31,
    ensures -900000 <= r <= 3000000,
    returns days_from_civil(y, m, d)
))]
pub fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y1 = if m > 2 { y } else { y - 1 };
    let era = tdiv(if y1 >= 0 { y1 } else { y1 - 399 }, 400);
    let yoe = y1 - era * 400;
    let mp = if m > 2 { m - 3 } else { m + 9 };
    let doy = tdiv(153 * mp + 2, 5) + d - 1;
    let doe = yoe * 365 + tdiv(yoe, 4) - tdiv(yoe, 100) + doy;
    era * 146097 + doe - 719468
}

/// The value of optional (at most 4) ASCII digits (0 if absent)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns opt_small_nat(m)))]
pub fn opt_small_nat(m: &Option<Str>) -> i64 {
    match m {
        Some(m) => small_nat(m),
        None => 0,
    }
}

/// The seconds to add to a local time with the offset `off` to get UTC, if
/// the offset is valid (`UTCOffset::is_valid`)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Some(x) ==> -86_400 < x < 86_400,
    returns offset_delta(off)
))]
pub fn offset_delta(off: &Option<(bool, Str, Str)>) -> Option<i64> {
    match off {
        None => Some(0),
        Some((pos, hh, mm)) => {
            let oh = small_nat(hh);
            let om = small_nat(mm);
            if oh < 24 && om < 60 {
                let secs = oh * 3600 + om * 60;
                if *pos {
                    Some(0 - secs)
                } else {
                    Some(secs)
                }
            } else {
                None
            }
        }
    }
}

/// The time part of a datetime (`THH:MM:SS`, optional milliseconds, and a
/// zone): its contribution to the milliseconds since the epoch, if valid
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Some(x) ==> -86_400_000 < x < 2 * 86_400_000,
    returns parse_time(s)
))]
pub fn parse_time(s: &Str) -> Option<i64> {
    match match_hms(s) {
        None => None,
        Some((hs, mis, ss, rest)) => match match_ms_offset(&rest) {
            None => None,
            Some((msopt, off)) => {
                let h = small_nat(&hs);
                let mi = small_nat(&mis);
                let sec = small_nat(&ss);
                let ms = opt_small_nat(&msopt);
                match offset_delta(&off) {
                    None => None,
                    Some(dl) => {
                        if h < 24 && mi < 60 && sec < 60 {
                            Some(((h * 3600 + mi * 60 + sec) * 1000 + ms) + dl * 1000)
                        } else {
                            None
                        }
                    }
                }
            }
        },
    }
}

/// Production's `parse_datetime` followed by `DateTime::from` (Lean's
/// `Datetime.parse`): milliseconds since the epoch
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_datetime(s)))]
pub fn parse_datetime(s: &Str) -> Option<i64> {
    match match_date(s) {
        None => None,
        Some((ys, mos, ds, rest)) => {
            let y = small_nat(&ys);
            let mo = small_nat(&mos);
            let d = small_nat(&ds);
            if !valid_date(y, mo, d) {
                None
            } else if is_empty(&rest) {
                Some(days_from_civil(y, mo, d) * MS_PER_DAY)
            } else {
                match parse_time(&rest) {
                    None => None,
                    Some(t) => Some(days_from_civil(y, mo, d) * MS_PER_DAY + t),
                }
            }
        }
    }
}

/// `([0-9]+)u`: the digits, if the unit `u` follows them, and the rest. With
/// `no_s`, the unit must not be followed by `s` (to tell `m` from `ms`).
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns take_unit(s, u, no_s)))]
pub fn take_unit(s: &Str, u: char, no_s: bool) -> (Option<Str>, Str) {
    let (ds, rest) = span_digits(s);
    if is_empty(&ds) {
        (None, clone_str(s))
    } else {
        match &rest {
            List::Cons(c, rest2) => {
                if *c == u && !(no_s && starts_with(rest2, 's')) {
                    (Some(ds), clone_str(rest2))
                } else {
                    (None, clone_str(s))
                }
            }
            List::Nil => (None, clone_str(s)),
        }
    }
}

/// `([0-9]+)ms`: the digits, if `ms` follows them, and the rest
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns take_ms(s)))]
pub fn take_ms(s: &Str) -> (Option<Str>, Str) {
    let (ds, rest) = span_digits(s);
    if is_empty(&ds) {
        (None, clone_str(s))
    } else {
        match take_char(&rest, 'm') {
            Some(r1) => match take_char(&r1, 's') {
                Some(r2) => (Some(ds), r2),
                None => (None, clone_str(s)),
            },
            None => (None, clone_str(s)),
        }
    }
}

/// Production's `DURATION_PATTERN`
/// (`^-?(([0-9]+)d)?(([0-9]+)h)?(([0-9]+)m)?(([0-9]+)s)?(([0-9]+)ms)?$`).
/// Matches are unique, so a greedy matcher finds the regex's captures.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns duration_regex(s)))]
pub fn duration_regex(s: &Str) -> Option<DurParts> {
    let body = match s {
        List::Cons(c, rest) => {
            if *c == '-' {
                clone_str(rest)
            } else {
                clone_str(s)
            }
        }
        List::Nil => List::Nil,
    };
    let (d, r1) = take_unit(&body, 'd', false);
    let (h, r2) = take_unit(&r1, 'h', false);
    let (m, r3) = take_unit(&r2, 'm', true);
    let (sec, r4) = take_unit(&r3, 's', false);
    let (ms, r5) = take_ms(&r4);
    if is_empty(&r5) {
        Some(DurParts { d, h, m, s: sec, ms })
    } else {
        None
    }
}

/// The quantity of a unit: 0 if absent, `None` if it does not fit in `u64`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns dur_quantity(q)))]
pub fn dur_quantity(q: &Option<Str>) -> Option<u64> {
    match q {
        None => Some(0),
        Some(ds) => parse_u64(ds),
    }
}

/// Production's `checked_op`: `acc ± y * mul`, checked
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns dur_step(acc, y, mul, neg)))]
pub fn dur_step(acc: i64, y: u64, mul: i64, neg: bool) -> Option<i64> {
    if y > 0x7fff_ffff_ffff_ffff {
        None
    } else {
        match (y as i64).checked_mul(mul) {
            None => None,
            Some(p) => {
                if neg {
                    acc.checked_sub(p)
                } else {
                    acc.checked_add(p)
                }
            }
        }
    }
}

/// The milliseconds of a duration with `ms` milliseconds:
/// `i64::try_from(-i128::from(ms))` if `neg`, `i64::try_from(ms)` otherwise
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns dur_init(ms, neg)))]
pub fn dur_init(ms: u64, neg: bool) -> Option<i64> {
    if neg {
        if ms <= 0x7fff_ffff_ffff_ffff {
            Some(0 - (ms as i64))
        } else if ms == 0x8000_0000_0000_0000 {
            Some(-0x7fff_ffff_ffff_ffff - 1)
        } else {
            None
        }
    } else if ms <= 0x7fff_ffff_ffff_ffff {
        Some(ms as i64)
    } else {
        None
    }
}

/// Production's `parse_duration` (Lean's `Duration.parse`): milliseconds
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns parse_duration(s)))]
pub fn parse_duration(s: &Str) -> Option<i64> {
    if is_empty(s) || is_char(s, '-') {
        None
    } else {
        match duration_regex(s) {
            None => None,
            Some(parts) => {
                let neg = starts_with(s, '-');
                match (
                    dur_quantity(&parts.d),
                    dur_quantity(&parts.h),
                    dur_quantity(&parts.m),
                    dur_quantity(&parts.s),
                    dur_quantity(&parts.ms),
                ) {
                    (Some(d), Some(h), Some(m), Some(sec), Some(ms)) => {
                        let ms0 = dur_init(ms, neg);
                        match ms0 {
                            None => None,
                            Some(a0) => match dur_step(a0, sec, 1000, neg) {
                                None => None,
                                Some(a1) => match dur_step(a1, m, 60_000, neg) {
                                    None => None,
                                    Some(a2) => match dur_step(a2, h, 3_600_000, neg) {
                                        None => None,
                                        Some(a3) => dur_step(a3, d, MS_PER_DAY, neg),
                                    },
                                },
                            },
                        }
                    }
                    _ => None,
                }
            }
        }
    }
}

/// `DateTime::offset`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns dt_offset(dt, dur)))]
pub fn dt_offset(dt: i64, dur: i64) -> Option<i64> {
    dt.checked_add(dur)
}

/// `DateTime::duration_since`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns dt_duration_since(a, b)))]
pub fn dt_duration_since(a: i64, b: i64) -> Option<i64> {
    a.checked_sub(b)
}

/// `DateTime::to_date`: `dt - dt.rem_euclid(MS_PER_DAY)`, checked
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns dt_to_date(dt)))]
pub fn dt_to_date(dt: i64) -> Option<i64> {
    let r = tmod(dt, MS_PER_DAY);
    let r = if r < 0 { r + MS_PER_DAY } else { r };
    dt.checked_sub(r)
}

/// `DateTime::to_time`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns dt_to_time(dt)))]
pub fn dt_to_time(dt: i64) -> i64 {
    if dt < 0 {
        let r = tmod(dt, MS_PER_DAY);
        if r == 0 {
            r
        } else {
            r + MS_PER_DAY
        }
    } else {
        tmod(dt, MS_PER_DAY)
    }
}

// ---------------------------------------------------------------------------
// Well-formedness, equality and ordering
// ---------------------------------------------------------------------------

/// IP prefixes are at most the address width (always true in production).
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ext_wf(e)))]
pub fn ext_wf(e: &Ext) -> bool {
    match e {
        Ext::IPAddr(IPNet::V4(_, p)) => *p <= 32,
        Ext::IPAddr(IPNet::V6(_, p)) => *p <= 128,
        _ => true,
    }
}

/// A prefix length clipped to 32, as in Lean's `IPNetPrefix.ofNat`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clip_v4(p)))]
pub fn clip_v4(p: u8) -> u8 {
    if p > 32 {
        32
    } else {
        p
    }
}

/// A prefix length clipped to 128
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clip_v6(p)))]
pub fn clip_v6(p: u8) -> u8 {
    if p > 128 {
        128
    } else {
        p
    }
}

/// Equality of networks (as Lean's: prefixes are clipped to the width)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ipnet_eq(a, b)))]
pub fn ipnet_eq(a: &IPNet, b: &IPNet) -> bool {
    match (a, b) {
        (IPNet::V4(x, p), IPNet::V4(y, q)) => *x == *y && clip_v4(*p) == clip_v4(*q),
        (IPNet::V6(x, p), IPNet::V6(y, q)) => *x == *y && clip_v6(*p) == clip_v6(*q),
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ext_eq(a, b)))]
pub fn ext_eq(a: &Ext, b: &Ext) -> bool {
    match (a, b) {
        (Ext::Decimal(x), Ext::Decimal(y)) => *x == *y,
        (Ext::IPAddr(x), Ext::IPAddr(y)) => ipnet_eq(x, y),
        (Ext::Datetime(x), Ext::Datetime(y)) => *x == *y,
        (Ext::Duration(x), Ext::Duration(y)) => *x == *y,
        _ => false,
    }
}

/// Lean's `IPNet.lt` (and production's derived order): V4 before V6, then by
/// address, then by prefix
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ipnet_lt(a, b)))]
pub fn ipnet_lt(a: &IPNet, b: &IPNet) -> bool {
    match (a, b) {
        (IPNet::V4(x, p), IPNet::V4(y, q)) => *x < *y || (*x == *y && clip_v4(*p) < clip_v4(*q)),
        (IPNet::V6(x, p), IPNet::V6(y, q)) => *x < *y || (*x == *y && clip_v6(*p) < clip_v6(*q)),
        (IPNet::V4(_, _), IPNet::V6(_, _)) => true,
        (IPNet::V6(_, _), IPNet::V4(_, _)) => false,
    }
}

/// Lean's `Ext.lt`: by value within a type, else by type name
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ext_lt(a, b)))]
pub fn ext_lt(a: &Ext, b: &Ext) -> bool {
    match (a, b) {
        (Ext::Decimal(x), Ext::Decimal(y)) => *x < *y,
        (Ext::IPAddr(x), Ext::IPAddr(y)) => ipnet_lt(x, y),
        (Ext::Datetime(x), Ext::Datetime(y)) => *x < *y,
        (Ext::Duration(x), Ext::Duration(y)) => *x < *y,
        // different types: by type name, datetime < decimal < duration < ipaddr
        (Ext::Datetime(_), _) => true,
        (Ext::Decimal(_), Ext::Duration(_)) => true,
        (Ext::Decimal(_), Ext::IPAddr(_)) => true,
        (Ext::Duration(_), Ext::IPAddr(_)) => true,
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_ipnet(a)))]
pub fn clone_ipnet(a: &IPNet) -> IPNet {
    match a {
        IPNet::V4(x, p) => IPNet::V4(*x, *p),
        IPNet::V6(x, p) => IPNet::V6(*x, *p),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_ext(e)))]
pub fn clone_ext(e: &Ext) -> Ext {
    match e {
        Ext::Decimal(x) => Ext::Decimal(*x),
        Ext::IPAddr(a) => Ext::IPAddr(clone_ipnet(a)),
        Ext::Datetime(x) => Ext::Datetime(*x),
        Ext::Duration(x) => Ext::Duration(*x),
    }
}

// ---------------------------------------------------------------------------
// Extension-function dispatch (`Cedar.Spec.call`)
// ---------------------------------------------------------------------------

/// Lean's `res`: a parse or overflow failure is an extension error
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ext_or_err(e)))]
pub fn ext_or_err(e: Option<Ext>) -> Result<ExtRes, Error> {
    match e {
        Some(x) => Ok(ExtRes::Ext(x)),
        None => Err(Error::ExtensionError),
    }
}

/// The only argument
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns one_arg(args)))]
pub fn one_arg(args: &List<Value>) -> Option<&Value> {
    match args {
        List::Cons(a, rest) => match &**rest {
            List::Nil => Some(a),
            List::Cons(_, _) => None,
        },
        List::Nil => None,
    }
}

/// The only two arguments
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns two_args(args)))]
pub fn two_args(args: &List<Value>) -> Option<(&Value, &Value)> {
    match args {
        List::Cons(a, rest) => match &**rest {
            List::Cons(b, rest2) => match &**rest2 {
                List::Nil => Some((a, b)),
                List::Cons(_, _) => None,
            },
            List::Nil => None,
        },
        List::Nil => None,
    }
}

/// Applies a unary function to a single string argument
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns call_string(f, args)))]
pub fn call_string(f: &ExtFun, args: &List<Value>) -> Result<ExtRes, Error> {
    match one_arg(args) {
        Some(Value::Prim(Prim::String(s))) => match f {
            ExtFun::Decimal => ext_or_err(match parse_decimal(s) {
                Some(d) => Some(Ext::Decimal(d)),
                None => None,
            }),
            ExtFun::Ip => ext_or_err(match parse_ip(s) {
                Some(a) => Some(Ext::IPAddr(a)),
                None => None,
            }),
            ExtFun::Datetime => ext_or_err(match parse_datetime(s) {
                Some(d) => Some(Ext::Datetime(d)),
                None => None,
            }),
            ExtFun::Duration => ext_or_err(match parse_duration(s) {
                Some(d) => Some(Ext::Duration(d)),
                None => None,
            }),
            _ => Err(Error::TypeError),
        },
        _ => Err(Error::TypeError),
    }
}

/// The decimal comparisons
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns call_decimal_cmp(f, args)))]
pub fn call_decimal_cmp(f: &ExtFun, args: &List<Value>) -> Result<ExtRes, Error> {
    match two_args(args) {
        Some((Value::Ext(Ext::Decimal(x)), Value::Ext(Ext::Decimal(y)))) => match f {
            ExtFun::LessThan => Ok(ExtRes::Bool(*x < *y)),
            ExtFun::LessThanOrEqual => Ok(ExtRes::Bool(*x <= *y)),
            ExtFun::GreaterThan => Ok(ExtRes::Bool(*x > *y)),
            ExtFun::GreaterThanOrEqual => Ok(ExtRes::Bool(*x >= *y)),
            _ => Err(Error::TypeError),
        },
        _ => Err(Error::TypeError),
    }
}

/// The unary IP predicates
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns call_ip_pred(f, args)))]
pub fn call_ip_pred(f: &ExtFun, args: &List<Value>) -> Result<ExtRes, Error> {
    match one_arg(args) {
        Some(Value::Ext(Ext::IPAddr(a))) => match f {
            ExtFun::IsIpv4 => Ok(ExtRes::Bool(ip_is_v4(a))),
            ExtFun::IsIpv6 => Ok(ExtRes::Bool(ip_is_v6(a))),
            ExtFun::IsLoopback => Ok(ExtRes::Bool(ip_is_loopback(a))),
            ExtFun::IsMulticast => Ok(ExtRes::Bool(ip_is_multicast(a))),
            _ => Err(Error::TypeError),
        },
        _ => Err(Error::TypeError),
    }
}

/// The unary duration conversions
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns call_duration_conv(f, args)))]
pub fn call_duration_conv(f: &ExtFun, args: &List<Value>) -> Result<ExtRes, Error> {
    match one_arg(args) {
        Some(Value::Ext(Ext::Duration(x))) => match f {
            ExtFun::ToMilliseconds => Ok(ExtRes::Int(*x)),
            ExtFun::ToSeconds => Ok(ExtRes::Int(tdiv(*x, 1000))),
            ExtFun::ToMinutes => Ok(ExtRes::Int(tdiv(tdiv(*x, 1000), 60))),
            ExtFun::ToHours => Ok(ExtRes::Int(tdiv(tdiv(tdiv(*x, 1000), 60), 60))),
            ExtFun::ToDays => Ok(ExtRes::Int(tdiv(tdiv(tdiv(tdiv(*x, 1000), 60), 60), 24))),
            _ => Err(Error::TypeError),
        },
        _ => Err(Error::TypeError),
    }
}

/// Lean's `Cedar.Spec.call`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns call(f, args)))]
pub fn call(f: &ExtFun, args: &List<Value>) -> Result<ExtRes, Error> {
    match f {
        ExtFun::Decimal | ExtFun::Ip | ExtFun::Datetime | ExtFun::Duration => call_string(f, args),
        ExtFun::LessThan
        | ExtFun::LessThanOrEqual
        | ExtFun::GreaterThan
        | ExtFun::GreaterThanOrEqual => call_decimal_cmp(f, args),
        ExtFun::IsIpv4 | ExtFun::IsIpv6 | ExtFun::IsLoopback | ExtFun::IsMulticast => {
            call_ip_pred(f, args)
        }
        ExtFun::IsInRange => match two_args(args) {
            Some((Value::Ext(Ext::IPAddr(a)), Value::Ext(Ext::IPAddr(b)))) => {
                Ok(ExtRes::Bool(ip_in_range(a, b)))
            }
            _ => Err(Error::TypeError),
        },
        ExtFun::Offset => match two_args(args) {
            Some((Value::Ext(Ext::Datetime(dt)), Value::Ext(Ext::Duration(dur)))) => {
                ext_or_err(match dt_offset(*dt, *dur) {
                    Some(x) => Some(Ext::Datetime(x)),
                    None => None,
                })
            }
            _ => Err(Error::TypeError),
        },
        ExtFun::DurationSince => match two_args(args) {
            Some((Value::Ext(Ext::Datetime(a)), Value::Ext(Ext::Datetime(b)))) => {
                ext_or_err(match dt_duration_since(*a, *b) {
                    Some(x) => Some(Ext::Duration(x)),
                    None => None,
                })
            }
            _ => Err(Error::TypeError),
        },
        ExtFun::ToDate => match one_arg(args) {
            Some(Value::Ext(Ext::Datetime(dt))) => ext_or_err(match dt_to_date(*dt) {
                Some(x) => Some(Ext::Datetime(x)),
                None => None,
            }),
            _ => Err(Error::TypeError),
        },
        ExtFun::ToTime => match one_arg(args) {
            Some(Value::Ext(Ext::Datetime(dt))) => Ok(ExtRes::Ext(Ext::Duration(dt_to_time(*dt)))),
            _ => Err(Error::TypeError),
        },
        ExtFun::ToMilliseconds
        | ExtFun::ToSeconds
        | ExtFun::ToMinutes
        | ExtFun::ToHours
        | ExtFun::ToDays => call_duration_conv(f, args),
    }
}
