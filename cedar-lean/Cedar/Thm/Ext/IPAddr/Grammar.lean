module

public import Cedar.Spec.Ext.IPAddr
public import Cedar.Thm.Data.String

import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.IPAddr
import all Cedar.Thm.Data.String

namespace Cedar.Thm.IPAddr
open Cedar.Spec.Ext
open IPAddr

/-! # IPAddr grammar: definitions

This file contains only the grammar-level definitions — the well-formedness predicates and the
value function — as a direct, parser-independent transcription of the IP-address grammar accepted
by `Cedar.Spec.Ext.IPAddr.parse`. The lemmas connecting these definitions to `IPAddr.parse` live in
`Cedar.Thm.Ext.IPAddr.Lemmas`. The `Digit⁺` predicate `IsDigits` is shared with the decimal,
duration, and datetime grammars and lives in `Cedar.Thm.Data.String`.

The accepted syntax (transcribed from the spec parser) is, informally:

```
IPNet    ::= V4Net | V6Net          -- V4 tried first; a string is V6 only if it is not V4
V4Net    ::= V4Addr ['/' V4Prefix]
V4Addr   ::= NumV4 '.' NumV4 '.' NumV4 '.' NumV4
NumV4    ::= Digit{1,3}             -- no leading zeros unless the group is exactly "0"; value ≤ 255
V4Prefix ::= Digit{1,2}            -- no leading zeros unless exactly "0"; value ≤ 32

V6Net    ::= V6Addr ['/' V6Prefix]
V6Addr   ::= a `::`-compressed sequence of hextets that expands to exactly 8 groups
NumV6    ::= HexDigit{1,4}          -- value ≤ 0xffff (automatic from ≤ 4 hex digits)
V6Prefix ::= Digit{1,3}            -- no leading zeros unless exactly "0"; value ≤ 128
```

The `::` compression may appear at most once and denotes a run of zero hextets that pads the total
to 8 groups. -/

/-! ## Shared digit/number-token predicates -/

/-- A `Digit⁺` string that additionally forbids a leading zero unless it is exactly `"0"` — the
    "no leading zeros" rule the spec parser enforces on every numeric group and prefix
    (`str.startsWith "0" → str = "0"`). -/
-- ANCHOR: IsCanonicalNat
public def IsCanonicalNat (s : String) : Prop :=
  IsDigits s ∧ (s.startsWith "0" → s = "0")
-- ANCHOR_END: IsCanonicalNat

/-- Numeric value of a digit-string group, defaulting to `0` when it does not parse (never taken on
    a `IsDigits` group). -/
-- ANCHOR: numValue
public def numValue (s : String) : Nat := (toNat?' s).getD 0
-- ANCHOR_END: numValue

/-! ## IPv4 grammar

`V4Addr` is four dot-separated groups, each a canonical 1–3 digit number `≤ 255`; the optional
prefix is a canonical 1–2 digit number `≤ 32`. -/

/-- The grammar's `V4Addr ::= NumV4 '.' NumV4 '.' NumV4 '.' NumV4`: four decimal groups. -/
-- ANCHOR: V4Components
public structure V4Components where
  g₀ : String
  g₁ : String
  g₂ : String
  g₃ : String
-- ANCHOR_END: V4Components

/-- Each group is a canonical number of at most 3 digits. -/
-- ANCHOR: V4Components.syntaxWf
public def V4Components.syntaxWf (v : V4Components) : Prop :=
  (IsCanonicalNat v.g₀ ∧ v.g₀.length ≤ 3) ∧
  (IsCanonicalNat v.g₁ ∧ v.g₁.length ≤ 3) ∧
  (IsCanonicalNat v.g₂ ∧ v.g₂.length ≤ 3) ∧
  (IsCanonicalNat v.g₃ ∧ v.g₃.length ≤ 3)
-- ANCHOR_END: V4Components.syntaxWf

/-- Each group's value is at most `255` (`0xff`). -/
-- ANCHOR: V4Components.constraintsWf
public def V4Components.constraintsWf (v : V4Components) : Prop :=
  numValue v.g₀ ≤ 255 ∧ numValue v.g₁ ≤ 255 ∧ numValue v.g₂ ≤ 255 ∧ numValue v.g₃ ≤ 255
-- ANCHOR_END: V4Components.constraintsWf

/-- Render a `V4Addr` as `g₀ '.' g₁ '.' g₂ '.' g₃`. -/
-- ANCHOR: V4Components.asString
public def V4Components.asString (v : V4Components) : String :=
  v.g₀ ++ "." ++ v.g₁ ++ "." ++ v.g₂ ++ "." ++ v.g₃
-- ANCHOR_END: V4Components.asString

/-- The `IPv4Addr` value of well-formed V4 groups. -/
-- ANCHOR: V4Components.toAddr
public def V4Components.toAddr (v : V4Components) : IPv4Addr :=
  IPv4Addr.mk (numValue v.g₀) (numValue v.g₁) (numValue v.g₂) (numValue v.g₃)
-- ANCHOR_END: V4Components.toAddr

/-! ## IPv6 grammar

`V6Addr` is a `::`-compressed sequence of hextets. Rather than model the compression syntactically
here, a `V6Components` record holds the eight expanded hextets together with the *rendering* (the
concrete `::`-form string), and well-formedness is phrased existentially over that rendering (as in
the duration/datetime grammars). Each hextet is a 1–4 character hex-digit string. -/

/-- A `Digit⁺`-style predicate for hex groups: a non-empty string all of whose characters are hex
    digits, of length at most 4. -/
-- ANCHOR: IsHexGroup
public def IsHexGroup (s : String) : Prop :=
  0 < s.length ∧ s.length ≤ 4 ∧ ∀ c ∈ s.toList, isHexDigit c = true
-- ANCHOR_END: IsHexGroup

/-- Numeric value of a hex group (`Σ digit · 16ⁱ`), matching the spec parser's `foldl`. -/
-- ANCHOR: hexValue
public def hexValue (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + toHexNat c) 0
-- ANCHOR_END: hexValue

/-- A V6 address, as the spec parser accepts it: either a full list of hextets with no `::`
    compression, or a `::`-compressed form with a left and right list of hextets and an implicit
    run of zero hextets between them. This mirrors `parseSegsV6`'s `splitOn "::"`:
    - `full gs`     ↔ the string has no `::`; `gs` is the `':'`-separated hextet list;
    - `gap l r`     ↔ the string is `l₀:…:lₘ '::' r₀:…:rₙ`; the gap expands to `8 − (|l|+|r|)`
      zero hextets. -/
-- ANCHOR: V6Components
public inductive V6Components where
  | full (gs : List String)
  | gap  (l r : List String)
-- ANCHOR_END: V6Components

/-- The eight expanded hextet strings a `V6Components` denotes: the full list itself, or the two
    sides padded with the appropriate number of `"0"` hextets between them. -/
-- ANCHOR: V6Components.expand
public def V6Components.expand : V6Components → List String
  | .full gs  => gs
  | .gap l r  => l ++ List.replicate (8 - (l.length + r.length)) "0" ++ r
-- ANCHOR_END: V6Components.expand

/-- Syntactic well-formedness of a V6 address:
    - every present hextet is a valid 1–4 digit hex group;
    - the `full` form has exactly 8 hextets (no `::` ⇒ `splitToList ':'` must give 8);
    - the `gap` form's two sides total *strictly fewer* than 8 (so the `::` denotes ≥ 1 zero
      hextet — `parseSegsV6` requires `len < 8`). -/
-- ANCHOR: V6Components.syntaxWf
public def V6Components.syntaxWf : V6Components → Prop
  | .full gs => gs.length = 8 ∧ ∀ s ∈ gs, IsHexGroup s
  | .gap l r => l.length + r.length < 8 ∧ (∀ s ∈ l, IsHexGroup s) ∧ (∀ s ∈ r, IsHexGroup s)
-- ANCHOR_END: V6Components.syntaxWf

/-- Render a V6 address to its concrete string: hextets joined by `':'`, with `"::"` at the gap.
    (`intercalate ":"` matches the parser's `splitToList (· = ':')` / `splitOn "::"` inverse.) -/
-- ANCHOR: V6Components.asString
public def V6Components.asString : V6Components → String
  | .full gs => String.intercalate ":" gs
  | .gap l r => String.intercalate ":" l ++ "::" ++ String.intercalate ":" r
-- ANCHOR_END: V6Components.asString

/-- The `IPv6Addr` value: the eight expanded hextets' hex values. Well-formedness guarantees
    `expand` has length 8; on other lengths this defaults the missing groups to `0`. -/
-- ANCHOR: V6Components.toAddr
public def V6Components.toAddr (v : V6Components) : IPv6Addr :=
  let g := v.expand
  let hx (i : Nat) : Nat := hexValue (g.getD i "0")
  IPv6Addr.mk (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) (hx 5) (hx 6) (hx 7)
-- ANCHOR_END: V6Components.toAddr

/-! ## Prefix grammar

An optional CIDR suffix `'/' Prefix`, where `Prefix` is a canonical decimal number bounded by the
address width (`≤ 32` for V4, `≤ 128` for V6). Absence of the suffix denotes the full-width prefix
(`ADDR_SIZE`). -/

/-- The optional prefix, with its digit-count and value bounds `(digits, size)`
    (`(2, 32)` for V4, `(3, 128)` for V6). `none` is the implicit full-width prefix. -/
-- ANCHOR: IsWfOptionalPrefix
public def IsWfOptionalPrefix (digits size : Nat) : Option String → Prop
  | none        => True
  | some p      => IsCanonicalNat p ∧ p.length ≤ digits ∧ numValue p ≤ size
-- ANCHOR_END: IsWfOptionalPrefix

/-- The `IPNetPrefix` value of an optional prefix string: `none` maps to the full-width prefix. -/
-- ANCHOR: prefixValue
public def prefixValue (w : Nat) : Option String → IPNetPrefix w
  | none   => IPNetPrefix.ofNat w (ADDR_SIZE w)
  | some p => IPNetPrefix.ofNat w (numValue p)
-- ANCHOR_END: prefixValue

/-! ## Top-level well-formedness

An IP-net string is well-formed when it is either a well-formed V4 rendering or a well-formed V6
rendering (with V4 taking precedence, mirroring the parser's `if ipv4.isSome then … else …`). Both
are phrased existentially over the components' `asString` rendering (as in the duration/datetime
grammars), baking the separators, group count, and `::`-compression rules into the witness. -/

/-- Well-formed IPv4-net string: `addr ['/' pre]` where `addr` renders well-formed V4 groups whose
    values are in range, and the optional prefix is a canonical `≤ 32` number. -/
-- ANCHOR: IsWfV4
public def IsWfV4 (str : String) : Prop :=
  ∃ (v : V4Components) (pre : Option String),
    v.syntaxWf ∧ v.constraintsWf ∧
    IsWfOptionalPrefix 2 (ADDR_SIZE V4_WIDTH) pre ∧
    str = v.asString ++ (match pre with | none => "" | some p => "/" ++ p)
-- ANCHOR_END: IsWfV4

/-- Well-formed IPv6-net string: `addr ['/' pre]` where `addr` is the `asString` rendering of a
    syntactically well-formed `V6Components` (either 8 `':'`-separated hextets, or a `::`-compressed
    form whose two sides total `< 8`), and the optional prefix is a canonical `≤ 128` number. -/
-- ANCHOR: IsWfV6
public def IsWfV6 (str : String) : Prop :=
  ∃ (v : V6Components) (pre : Option String),
    v.syntaxWf ∧
    IsWfOptionalPrefix 3 (ADDR_SIZE V6_WIDTH) pre ∧
    str = v.asString ++ (match pre with | none => "" | some p => "/" ++ p)
-- ANCHOR_END: IsWfV6

/-- A string is a well-formed IP-net iff it is a well-formed V4 or V6 net. Because the parser tries
    V4 first and only falls through to V6 when V4 fails, and the two grammars are disjoint on their
    accepted strings, this disjunction faithfully characterizes acceptance. -/
-- ANCHOR: IsWfIPNet
public def IsWfIPNet (str : String) : Prop :=
  IsWfV4 str ∨ IsWfV6 str
-- ANCHOR_END: IsWfIPNet

/-! ## Value function

`computeValue` maps a well-formed string to the `IPNet` it denotes, independently of the parser.
For V4: the four groups' values form the address, with the optional prefix (defaulting to full
width). For V6: the eight hextets' values, similarly. It returns `none` on strings that match no
grammar form. -/

/-- The `IPNet` value of a well-formed V4 string's components. -/
-- ANCHOR: v4Value
public def v4Value (v : V4Components) (pre : Option String) : IPNet :=
  IPNet.V4 ⟨v.toAddr, prefixValue V4_WIDTH pre⟩
-- ANCHOR_END: v4Value

/-- The `IPNet` value of a well-formed V6 string's components. -/
-- ANCHOR: v6Value
public def v6Value (v : V6Components) (pre : Option String) : IPNet :=
  IPNet.V6 ⟨v.toAddr, prefixValue V6_WIDTH pre⟩
-- ANCHOR_END: v6Value

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed inputs. -/
public def normalize (str : String) : Option String := (IPAddr.ip str).map toString

end Cedar.Thm.IPAddr
