import VersoManual
import CedarDoc.GrammarBlock
import Cedar.Thm.Ext.IPAddr

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Cedar.Thm.IPAddr
open CedarDoc

set_option verso.code.warnLineLength 80

-- Source project for `module`/`anchor` code blocks: the sibling `cedar-lean`
-- package, relative to this doc's Lake workspace. These blocks render the real
-- imported definitions (true namespaces and bodies) straight from source.
set_option verso.exampleProject ".."

#doc (Manual) "IP Address Parsing" =>

Cedar IP-address values (`ipaddr`) represent an IPv4 or IPv6 network — an address together with an optional CIDR prefix. They are constructed from a string with the `ip()` operator, e.g. `ip("192.168.1.100")` or `ip("1:2:3:4::/48")`.

# Grammar

The accepted syntax for IP-address literals is:

```grammar
grammar
  IPNet    ::= V4Net | V6Net           -- V4 is tried first; a string is V6 only
                                       --   if it is not accepted as V4

  V4Net    ::= V4Addr ['/' V4Prefix]
  V4Addr   ::= NumV4 '.' NumV4 '.' NumV4 '.' NumV4
  NumV4    ::= Digit{1,3}
  V4Prefix ::= Digit{1,2}

  V6Net    ::= V6Addr ['/' V6Prefix]
  V6Addr   ::= H16 (':' H16){7}                        -- 8 groups, no '::'
             | [H16 (':' H16)*] '::' [H16 (':' H16)*]  -- one '::', sides total < 8
  H16      ::= HexDigit{1,4}
  V6Prefix ::= Digit{1,3}

  Digit    ::= '0' | '1' | … | '9'
  HexDigit ::= Digit | 'a'…'f' | 'A'…'F'

value
  value(V4Net) = the IPv4 address whose four octets are the NumV4 values,
                 with prefix nat(V4Prefix) (32 when '/' is absent)
  value(V6Net) = the IPv6 address whose eight hextets are the H16 hex values
                 (the '::' gap expanding to the missing zero hextets),
                 with prefix nat(V6Prefix) (128 when '/' is absent)

constraints
  - each NumV4 ≤ 255,  V4Prefix ≤ 32
  - each H16   ≤ 0xffff (automatic from ≤ 4 hex digits), V6Prefix ≤ 128
  - a numeric group or prefix may not have a leading zero unless it is
    exactly "0" (`str.startsWith "0" → str = "0"`)
  - '::' appears at most once; it stands for one or more all-zero H16 groups
    (the two sides must total strictly fewer than 8 groups)
```

A string is _valid_ if and only if it satisfies the grammar and constraints above. The `ip()` constructor tries the IPv4 grammar first and only falls through to IPv6 when the IPv4 parse fails; the two grammars accept disjoint sets of strings.

## Relationship to the IETF text representation

Cedar's grammar aligns with the IETF draft _Text Representation of IPv4 and IPv6 Addresses_ (`draft-main-ipaddr-text-rep-00`) on the numeric-token rules — IPv4 octets `0`–`255` with no leading zeros, IPv6 `H16` groups of one to four case-insensitive hex digits, and `::` used at most once for a run of one or more zero groups. It deliberately differs in two ways:

- *No embedded IPv4 in IPv6.* The IETF `ls32` production makes forms like `::ffff:1.2.3.4` canonical; Cedar rejects them — every IPv6 group must be pure hexadecimal (so `ip("::ffff:127.0.0.1")` is invalid).
- *CIDR prefix.* The IETF grammar covers only bare addresses; Cedar extends every address with an optional `'/'`-prefix suffix.

The address-generation _recommendations_ of the IETF draft (lowercase, omit leading zeros, and
elide the longest zero run) are not parser constraints. Cedar's canonical `toString` representation
instead uses fixed-width lowercase hextets and does not elide zero runs.

# Formal Specification

We formalize the validity of an input string by the predicate `IsWfIPNet` (well-formed syntax of the grammar) and the value functions `v4Value`/`v6Value` (the `IPNet` a well-formed string denotes). Unlike the decimal grammar, whose value is a single `Int`, an IP-net's value is an `IPNet`, so soundness and completeness are phrased per witnessing components rather than through a single `computeValue`.

The building block for numeric groups is `IsCanonicalNat`, which captures a non-empty digit string with the grammar's "no leading zeros" rule (`str.startsWith "0" → str = "0"`), building on the shared `IsDigits` predicate:

```anchor IsCanonicalNat (module := Cedar.Thm.Ext.IPAddr.Grammar)
public def IsCanonicalNat (s : String) : Prop :=
  IsDigits s ∧ (s.startsWith "0" → s = "0")
```

An IPv4 address is four decimal groups; `syntaxWf` pins each group to a canonical `Digit{1,3}` string and `constraintsWf` bounds each value by `255`:

```anchor V4Components.syntaxWf (module := Cedar.Thm.Ext.IPAddr.Grammar)
public def V4Components.syntaxWf (v : V4Components) : Prop :=
  (IsCanonicalNat v.g₀ ∧ v.g₀.length ≤ 3) ∧
  (IsCanonicalNat v.g₁ ∧ v.g₁.length ≤ 3) ∧
  (IsCanonicalNat v.g₂ ∧ v.g₂.length ≤ 3) ∧
  (IsCanonicalNat v.g₃ ∧ v.g₃.length ≤ 3)
```

```anchor V4Components.constraintsWf (module := Cedar.Thm.Ext.IPAddr.Grammar)
public def V4Components.constraintsWf (v : V4Components) : Prop :=
  numValue v.g₀ ≤ 255 ∧ numValue v.g₁ ≤ 255 ∧ numValue v.g₂ ≤ 255 ∧ numValue v.g₃ ≤ 255
```

An IPv6 address is modelled on the grammar's `::` structure — either a `full` list of eight groups, or a `gap` form whose two sides straddle the `::` and whose total is strictly fewer than eight groups (the gap expanding to the missing zero groups). This mirrors how the parser (next section) splits on `"::"`:

```anchor V6Components (module := Cedar.Thm.Ext.IPAddr.Grammar)
public inductive V6Components where
  | full (gs : List String)
  | gap  (l r : List String)
```

```anchor V6Components.syntaxWf (module := Cedar.Thm.Ext.IPAddr.Grammar)
public def V6Components.syntaxWf : V6Components → Prop
  | .full gs => gs.length = 8 ∧ ∀ s ∈ gs, IsHexGroup s
  | .gap l r => l.length + r.length < 8 ∧ (∀ s ∈ l, IsHexGroup s) ∧ (∀ s ∈ r, IsHexGroup s)
```

The optional CIDR prefix is a canonical decimal number bounded by the address width, with absence denoting the full-width prefix:

```anchor IsWfOptionalPrefix (module := Cedar.Thm.Ext.IPAddr.Grammar)
public def IsWfOptionalPrefix (digits size : Nat) : Option String → Prop
  | none        => True
  | some p      => IsCanonicalNat p ∧ p.length ≤ digits ∧ numValue p ≤ size
```

Well-formedness of the whole string then reads off the grammar — a well-formed V4 rendering or a well-formed V6 rendering, each phrased existentially over the components' `asString` (which bakes in the separators, group count, and `::`-placement):

```anchor IsWfV4 (module := Cedar.Thm.Ext.IPAddr.Grammar)
public def IsWfV4 (str : String) : Prop :=
  ∃ (v : V4Components) (pre : Option String),
    v.syntaxWf ∧ v.constraintsWf ∧
    IsWfOptionalPrefix 2 (ADDR_SIZE V4_WIDTH) pre ∧
    str = v.asString ++ (match pre with | none => "" | some p => "/" ++ p)
```

```anchor IsWfIPNet (module := Cedar.Thm.Ext.IPAddr.Grammar)
public def IsWfIPNet (str : String) : Prop :=
  IsWfV4 str ∨ IsWfV6 str
```

# Parser

```lean -show
-- Bring the spec's `IPNet` type and `IPAddr.ip` into scope for the executable
-- `#eval` examples below. The definitions themselves are shown from source via
-- `anchor` blocks, so nothing is redeclared here.
open Cedar.Spec.Ext.IPAddr
```

`IPAddr.ip` (a.k.a. `parse`) returns `some net` when the input string is valid, and `none` otherwise. It tries the IPv4 grammar first, falling through to IPv6 (shown here directly from source in `Cedar.Spec.Ext.IPAddr`):

```anchor parse (module := Cedar.Spec.Ext.IPAddr)
private def parse (str : String) : Option IPNet :=
  let ip := parseIPv4Net str
  if ip.isSome then ip else parseIPv6Net str
```

The IPv4 path splits off an optional `'/'` prefix, then parses four `'.'`-separated decimal groups; each group parser `parseNumV4` enforces the length, leading-zero, and `≤ 255` rules:

```anchor parseNumV4 (module := Cedar.Spec.Ext.IPAddr)
private def parseNumV4 (str : String) : Option (BitVec 8) :=
  let len := str.length
  if 0 < len && len ≤ 3 && (str.startsWith "0" → str = "0")
  then do
    let n ← toNat?' str
    if n ≤ 0xff then .some n else .none
  else .none
```

The IPv6 path handles `::` compression by splitting on `"::"`: with no `::` the address must be
exactly eight `':'`-separated groups; with one `::` the two sides are padded with zero groups to
reach eight (and are rejected if they already total eight):

```anchor parseSegsV6 (module := Cedar.Spec.Ext.IPAddr)
private def parseSegsV6 (str : String) : Option IPv6Addr := do
  let segs ←
    match str.splitOn "::" with
    | [s₁] => parseNumSegsV6 s₁
    | [s₁, s₂] => do
      let ns₁ ← parseNumSegsV6 s₁
      let ns₂ ← parseNumSegsV6 s₂
      let len := ns₁.length + ns₂.length
      if len < 8
      then .some (ns₁ ++ (List.replicate (8 - len) 0) ++ ns₂)
      else .none
    | _ => .none
  match segs with
  | [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇] =>
    .some (IPv6Addr.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇)
  | _ => .none
```

For example:

```lean (name := ex1)
#eval (ip "192.168.0.1/32").map toString    -- valid V4 with prefix
```
```leanOutput ex1
some "192.168.0.1/32"
```

```lean (name := ex2)
#eval (ip "F:AE::F:5:F:F:0").map toString    -- valid V6 with `::`
```
```leanOutput ex2
some "000f:00ae:0000:000f:0005:000f:000f:0000/128"
```

```lean (name := ex3)
#eval ip "256.0.0.1"                          -- octet out of range
```
```leanOutput ex3
none
```

```lean (name := ex4)
#eval ip "::ffff:127.0.0.1"                   -- no embedded IPv4
```
```leanOutput ex4
none
```

# Soundness and Completeness

The parser is characterized by the same guarantees as the other verified extension parsers. The
specification is independent of the parser: `IsWfIPNet` describes the accepted grammar, while
`v4Value` and `v6Value` give the value of witnessing components. The proof connects those
definitions to the hand-written parser, including IPv4's precedence over IPv6.

_Soundness_: whenever parsing succeeds, the input is well-formed and the returned `IPNet` is the
value of either witnessing IPv4 or IPv6 components.

{docstring parse_sound}

_Completeness_ is exact for each address family: well-formed IPv4 and IPv6 renderings parse to their
component values.

{docstring parse_complete_v4}

{docstring parse_complete_v6}

The family-independent form states that every well-formed IP-net string is accepted.

{docstring parse_complete}

Together, soundness and completeness characterize failure completely. There is no separate
overflow case: the octet, hextet, and prefix bounds are already part of the grammar.

{docstring parse_eq_none_iff}

# Canonical String Representation

`toString` converts an `IPNet` back to a canonical string: an IPv4 net prints its four decimal
octets and prefix; an IPv6 net prints all eight groups as four-digit lowercase hextets (no `::`
elision) and prefix.

```lean (name := ex5)
#eval toString ((ip "1:2:3:4:a:b:c:d/128").get!)
```
```leanOutput ex5
"0001:0002:0003:0004:000a:000b:000c:000d/128"
```

`normalize` composes parsing and serialization: it accepts any valid IP-net string and returns its
canonical form.

{docstring normalize}

{docstring toString_injective}

{docstring normalize_eq_iff_parse_eq}

# Roundtrip Theorem

Parsing the canonical string representation of any `IPNet` recovers the original value. This is the
headline user-facing property: `IPAddr.ip` and `toString` are mutually inverse on IP-net values,
and it is what underpins `toString_injective` above.

{docstring parse_toString_roundtrip}

The proof constructs well-formed canonical IPv4 or IPv6 components from the stored address and
prefix, applies completeness, and shows that the packed `BitVec` address and prefix are recovered
exactly.

All theorems above are machine-checked, contain no proof placeholders, and rely only on the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
