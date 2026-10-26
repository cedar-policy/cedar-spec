# The trusted base

Everything the end-to-end proof assumes rather than proves, beyond the
tools themselves (Lean's kernel, Verus and its SMT solver, Charon/Aeneas and
`vstd`). The [README](README.md) gives the theorem chain; this file lists
every assumption the chain depends on, grouped as follows:

1. the standard-library and third-party-library layer;
2. the behavior of derived traits (`PartialEq`, `Clone`, `Hash`, `Ord`);
3. the transcription of the Lean theorems to Verus;
4. the stack-depth check;
5. everything else: the extension-function registry, and specifications that
   claim nothing.

The assumptions live in four files of `cedar/cedar-policy-core/src/verification`:
`trusted.rs`, `ext_trusted.rs`, `authorizer_lean_theorems.rs`; in `cedar/cedar-policy/src/verification/trusted.rs`; and
in the `external_body` functions of the production code listed below.
Every `axiom fn`, `assume_specification`, `uninterp spec fn` with an axiom,
`PartialEqSpecImpl` and `external_body` function with an `ensures` clause is
listed here. `external_type_specification`s that are `external_body` declare
an opaque type and assume nothing about it. The transparent ones expose the
fields of a type, which Verus checks against its definition.

On the Lean side there is no assumption beyond Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). `scripts/check_axioms.sh`
checks this for every exported theorem. The extraction from Rust to Lean is
done by Aeneas, which is trusted, as is the Rust-to-Verus compilation. The
two hand-written Lean definitions of `FunsExternal.lean` are the two
functions Aeneas cannot translate. They are `value::char_lt` (`(c as u32) < (d as u32)`)
and `ext::char_code` (`c as u32`), and both are written as the Lean equivalent.

## Summary

| kind | count |
|---|---|
| `axiom fn` (Verus, excluding the Lean transcriptions) | 12 |
| `assume_specification` | 70 |
|   of which with an `ensures` clause | 55 |
| `uninterp spec fn` | 20 |
| `PartialEqSpecImpl` | 4 |
| production `external_body` with `ensures` (`cedar-policy-core`) | 23 |
| production `external_body` with `ensures` (`cedar-policy`) | 1 |
| Lean theorems transcribed as Verus axioms | 11 |
| Lean axioms beyond `propext`/`Classical.choice`/`Quot.sound` | 0 |

Everything else the proofs use is verified. In particular, the abstraction
functions from production types to model types (`value_abs.rs`,
`expr_abs.rs`, `policy_abs.rs`) are recursive spec functions, with
termination proved; the `Expr` constructors and accessors, the `Policy` and
`Template` accessors, `PartialResponse::concretize` and
`From<PartialResponse> for Response` are verified.

## 1. The standard-library and third-party-library layer

These specify code that is not part of Cedar and that `vstd` does not
specify (or does not specify in a form usable here). Each states the
documented behavior of the library function.

**`smol_str`** (`trusted.rs`):
- `smol_view` is the characters of a `SmolStr`.
- `smol_of_view` / `axiom_smol_view_injective`: a `SmolStr` is determined by its characters.
- `axiom_smol_str_cmp`: `==` compares characters, and `Ord` is lexicographic by code point, as for `str`.
- `axiom_smol_str_obeys_cmp`: `SmolStr`'s `Ord` is a lawful total order, which `vstd`'s `BTreeMap` specifications need for keys.
- `SmolStr::as_str`, `Deref`, `Clone`: return the same characters.
- `ToSmolStr::to_smolstr`: no claim.

A `SmolStr` is an immutable string whose comparisons delegate to `str`'s.

**Rust's `std`** (`trusted.rs`):
- `i64::checked_neg`;
- `Arc::as_ref`, which returns the pointee;
- `axiom_vec_into_iter_remaining`: iterating over a `Vec` by value yields its elements, in order. `vstd` has no `into_iter` specification for `Vec`.

**The data-structure layer of `Value`** (`trusted.rs`). A set value stores a
`BTreeSet<Value>`. `Value`'s `Eq`/`Ord` ignore the source location (they are
derived with `educe`), so `vstd`'s `BTreeSet` model doesn't apply: it needs
`Eq` to be structural equality. So the following are assumed:
- `set_elems(s)`, the iteration order, with `axiom_set_elems` (those are
  elements of the `BTreeSet`; this is what makes the abstraction of values
  terminate);
- `Set::is_empty`, `is_subset`, `is_disjoint`, `contains`, `iter`, stated on
  the abstraction (emptiness, inclusion, disjointness and membership of the
  model's lists);
- `value_set_from_vec` (`Value::set`, a collect into a `BTreeSet`), which
  sorts by `Value`'s `Ord` and removes duplicates. That is the model's
  `values_canonicalize`, because the derived `Ord` on values is the model's
  `value_lt`, and for extension values production's `cmp_extvalue` orders by
  type name, as the Lean spec's `Ext.lt` does.
- `value_record_from_vec` (`Value::record`, a collect into a
  `BTreeMap<SmolStr, Value>` of pairs with distinct keys), which sorts by
  key: the model's `attrs_canonicalize`. `vstd` has no specification of
  `collect` into a `BTreeMap`.

**The entity store** (`trusted.rs`):
- `abs_entities`, `abs_entity_data`, `entities_wf` and `entity_wf`;
- `Entities::entity`, `Entity::get`, `Entity::get_tag`, and
  `Entity::is_descendant_of`.

The store is a `HashMap<EntityUID, Arc<Entity>>`. An entity holds
`BTreeMap<SmolStr, PartialValue>`s of attributes and tags, and `HashSet`s of
ancestors. `EntityUID`'s `Eq`/`Hash` ignore the source location, so
`vstd`'s `HashMap` model doesn't apply. The specifications say that the
lookups are the model's `entities_find` / `attrs_find` / `uids_contains` on
the abstraction, for a concrete store (`entities_wf`: no residuals, no
partial entities). Entity-store construction is out of scope.

**Policy sets and responses** (`trusted.rs`):
- `pset_policies` and `PolicySet::policies`: iterating over the
  `LinkedHashMap` `links` yields each policy once, in a fixed order.
- `PartialResponse::new`: collecting the categorized policies
  (`impl IntoIterator`) into `HashMap`s keyed by policy ID, which is
  `FromIterator` for `HashMap`.

**The extension types** (`ext_trusted.rs`; see its header):
- the regexes: `decimal_parts`, `duration_parts`, `date_parts`,
  `hms_parts`, `ms_offset_parts` (in production, `external_body`), with
  `is_unicode_digit` / `axiom_unicode_digit`;
- `FromStr` for `i64`/`u64`/`u8`/`u32`/`i32`;
- `std::net::IpAddr::from_str` and the `IpAddr` predicates, with
  `v4_bits` / `v6_bits` and the `u32`/`u128` conversions;
- the `checked_*` integer operations, `is_negative`, `is_ascii_digit`, and
  `axiom_str_len_bound`;
- `chrono`'s `NaiveDate::from_ymd_opt`, `NaiveTime::from_hms(_milli)_opt`,
  `NaiveDateTime::new`, `TimeDelta::new`/`default`, `add_delta` and
  `of_naive` (production `external_body`), through `nd_days`, `nt_ms`,
  `ndt_ms`, `td_ms`;
- the `str` helpers `starts_with_char`, `str_eq`, `split_once_char`, and
  `contains_at_least_two` (production `external_body`).

**`cedar-policy`** (`cedar-policy/src/verification/trusted.rs`): opaque
types for `LinkedHashMap` and for the public `Policy`/`Template`. They only
appear in the redundant maps of the public `PolicySet`. The proofs use only
its core policy set.

## 2. Derived traits

The code generated by `derive` and `educe` is outside Verus. These state what
the derived code does:

- **`PartialEq`**:
  - `PartialEqSpecImpl` for `Value`: `value_peq` with `axiom_value_peq`.
    Equality of values is equality of their abstractions. The `educe`-derived
    `PartialEq` ignores the source location. Equality of extension values is
    `equals_extvalue`, which is false across types and the derived equality
    within one, as for the model's `Ext`.
  - `PartialEqSpecImpl` for `EntityUID`, `EntityType` and `Name`: equality
    is equality of the abstractions. Each compares its components, and
    `EntityUID` ignores its location.
- **`Hash` + `Eq`**: `axiom_slot_id_obeys_key_model` and
  `axiom_policy_id_obeys_key_model`. The derived `Hash`/`Eq` of `SlotId` and
  `PolicyID` obey `vstd`'s `HashMap` key model, so a `HashMap<SlotId, _>`
  (slot environments) and the `HashMap<PolicyID, _>`s of a
  `PartialResponse` behave as maps.
- **`Clone`**: `Value`, `PartialValue`, `Literal`, `EntityUID`,
  `EntityType`, `Expr`, `Request` and `PolicyID`. A derived `Clone` returns
  an equal value: their fields are `Arc`s, `SmolStr`s and plain data.

## 3. The Lean theorems, transcribed to Verus

`authorizer_lean_theorems.rs` states 11 `axiom fn`s. Each is the transcription of a
theorem proved in Lean about the extracted model
(`lean/CedarRustModel/Theorems/Authorization.lean`):

- `forbid_trumps_permit`, `allowed_only_if_explicitly_permitted`,
  `default_deny`;
- `allowed_iff_explicitly_permitted_and_not_denied`,
  `denied_iff_explicitly_denied_or_not_permitted`;
- `order_and_dup_independent`;
- `unchanged_allow_when_add_permit`, `unchanged_deny_when_add_forbid`;
- `is_authorized_eq_for_sound_policy_slice`;
- `determining_policies_of`, `erroring_policies_of`.

(`determining_erroring_disjoint_when_unique_ids` is proved in Verus from the
last two.)

The model functions are the same Rust source in both tools. The
transcription conventions are at the top of `authorizer_lean_theorems.rs`:
- `f x = ok r` is `f(x) == r`;
- `p ∈ List.toList ps` is `list_view(ps).contains(p)`;
- `IsLinked p` is `∃ lp, policy.to_policy lp = ok p`.

The trusted step is that each Verus statement means the same thing as the
Lean statement it names. The Lean side is checked: `lake build` proves the
theorems, and the axiom check confirms they use only the standard axioms.

## 4. The stack-depth check

`stack_exhausted()` is an uninterpreted proposition. `stack_size_check` is
specified to succeed when it is false (`trusted.rs`).

The evaluator calls `stack_size_check` before each recursive step. It
returns an error when `stacker::remaining_stack()` is below a threshold, and
then the evaluation fails with a recursion-limit error that the model does
not have.

The theorems assume `!stack_exhausted()`: they are about evaluations that
do not run out of stack. This is a precondition, not a claim about the code:
every result is a model result or the recursion-limit error. Recursive
production functions are proved for partial correctness
(`exec_allows_no_decreases_clause`).

## 5. Everything else

**The extension-function registry** (`evaluator.rs`, `external_body`):

- `call_extension_fn` is `extensions.func(fn_name)?.call(vals)`.
  - With all the extensions (`extensions_all`, which
    `Extensions::all_available` ensures), the function registered under each
    of the 22 names of `ext_abs::ext_fun_of_name` is the production function
    of `extensions/*.rs`. Each of those is verified against
    `ext::call` (in `extensions/{decimal,ipaddr,datetime}.rs`).
    `ExtensionFunction::call` checks the arity.
  - The registry is a `LazyLock` of `Extension` objects holding
    `Box<dyn Fn>`s. Verus cannot follow the dynamic dispatch, so the
    association of each name with its function is assumed.
- `ext_compare` is `x < y` / `x <= y` on two `Arc<RepresentableExtensionValue>`s
  of the same comparable type (`datetime`, `duration`). The `PartialOrd`
  goes through `dyn InternalExtensionValue::cmp_extvalue` to the derived
  `Ord` of `DateTime`/`Duration`, which compares the `i64` (`ext_cmp`).
- `ext_of`, `axiom_ext_of_wf`, `ext_typename`, `axiom_ext_typename`,
  `RepresentableExtensionValue::supports_operator_overloading` and
  `typename`, and the wrap/unwrap helpers (`decimal_value`, `as_decimal`,
  `ipaddr_value`, `as_ipaddr`, `datetime_value`, `as_datetime`,
  `duration_value`, `as_duration`, `datetime_output`, `duration_output`;
  production `external_body`).
  - A `RepresentableExtensionValue` is an `Arc<dyn InternalExtensionValue>`
    downcast with `Any`, which Verus cannot see into. `ext_of` is the model
    of the value it holds.
  - The axioms state that the IP prefixes production builds are bounded,
    and that the four type names are distinct.

**The public conversion of diagnostics** (`cedar-policy/src/api.rs`,
`external_body`): `From<authorizer::Diagnostics> for Diagnostics` keeps the
IDs of the determining policies and of the erroring policies. Its body is
`map(PolicyId::new).collect()` and `map(Into::into).collect()`, which Verus
does not support. `PolicyId::new` round-trips the ID through its string.

**Specifications that claim nothing.** These `assume_specification`s have
no `ensures` clause. They only let verified code call the function. The
calls are on paths the proofs do not use: residuals, error construction, or
partial evaluation.
- error construction: the `EvaluationError` constructors and
  `source_loc` / `with_maybe_source_loc`, and `Type::entity_type`;
- unknowns: `Unknown::new_untyped` / `new_with_type`;
- `Expr::is_projectable`;
- `Result::map_or_else` / `unwrap_or_else`.

The production `external_body` functions without `ensures` claim nothing
either. They are the error helpers of `evaluator.rs` and the extensions,
the residual builders, and the `ExprBuilder` methods `set`, `record`,
`call_extension_fn` and `error`.
