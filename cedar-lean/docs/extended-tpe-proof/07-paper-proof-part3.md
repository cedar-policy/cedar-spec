# Paper Proof Part 3: Target Correctness and Soundness

## 5. Target Correctness

The central lemma that makes the entire proof work.

### Definition 5.1 (Target Correctness)

A residual value `rv` is **target-correct** w.r.t. concrete entity store `E`, written `TC(rv, E)`, if for every `unknown(tgt, τ)` at attribute `a` within `rv` (at any nesting depth):

```
⟦tgt.a : τ⟧ᵣ_E = getAttr(⟦tgt⟧ᵣ_E, a, E)
```

and this equals the concrete value at that position.

More precisely, `TC` is defined inductively on `rv`:

```
TC(b, E)                                                   always
TC(uid, E)                                                 always
TC(rrec, E) where rrec = {a₁:ra₁,...}                     iff
  ∀(aᵢ, present(rvᵢ)) ∈ rrec : TC(rvᵢ, E)
  ∀(aᵢ, unknown(tgtᵢ, τᵢ)) ∈ rrec : ⟦tgtᵢ⟧ᵣ_E is defined
```

### Lemma 5.1 (toRV produces target-correct values)

If `E ≼_Γ PE` and `E, Γ ⊢ v ≼ pv` and `⟦tgt⟧ᵣ_E = Ok(v_container)` where `v_container` is the concrete record/entity containing the fields described by `pv`, then:

```
TC(toRV(tgt, pv, τ), E)
```

*Proof.* By induction on the structure of `pv`.

**Case `pv = b` or `pv = uid`:** `toRV` returns a primitive. `TC` holds trivially.

**Case `pv = prec`:** `toRV(tgt, prec, Record(rty))` produces a record `rrec` where:
- For `(a, present(pv'))`: the entry is `present(toRV(tgt.a : Record(rty), pv', rty(a)))`.
  The new target is `tgt.a : Record(rty)`.
  We need `⟦tgt.a : Record(rty)⟧ᵣ_E` to be defined.
  Since `⟦tgt⟧ᵣ_E = Ok(v_container)` and `a ∈ dom(v_container)` (by refinement, since `a` has a `present` entry), `getAttr(v_container, a, E)` succeeds.
  So `⟦tgt.a⟧ᵣ_E = Ok(v_container.a)`.
  By induction, `TC(toRV(tgt.a, pv', rty(a)), E)` holds.

- For `(a, unknown(τ'))`: the entry is `unknown(tgt, τ')`.
  We need `⟦tgt⟧ᵣ_E` to be defined. This is our hypothesis. □

### Lemma 5.2 (evalRV roundtrip for fully-concrete values)

If `rv = v.asRV` (a residual value derived from a concrete value with no unknown fields), then `evalRV(rv, E) = Ok(v)`.

*Proof.* By induction on `v`. Booleans and UIDs are immediate. For records, every field is `present(vᵢ.asRV)`, and by induction `evalRV(vᵢ.asRV, E) = Ok(vᵢ)`. □

### Lemma 5.3 (evalRV for target-correct values)

If `TC(rv, E)` and `rv` was produced by `toRV(tgt, pv, τ)` where `E, Γ ⊢ v ≼ pv` and `⟦tgt⟧ᵣ_E = Ok(v_container)` and `v_container` contains the concrete values corresponding to `pv`, then:

```
evalRV(rv, E) = Ok(v)
```

where `v` is the concrete value corresponding to `pv`.

*Proof.* By induction on `rv`.

**Case `rv = b` or `rv = uid`:** Immediate from `evalRV` definition.

**Case `rv = rrec`:** We must show each field evaluates correctly.

- For `(a, present(rv'))`: By induction, `evalRV(rv', E) = Ok(v')` where `v'` is the concrete value of attribute `a`. ✓

- For `(a, unknown(tgt, τ))`: By `evalRA`, we evaluate `⟦tgt.a : τ⟧ᵣ_E`.
  This is `getAttr(⟦tgt⟧ᵣ_E, a, E) = getAttr(v_container, a, E)`.
  Since `a` exists in the concrete container (by Lemma 4.3, the unknown attribute exists concretely), this returns `Ok(v_container.a)`. ✓

All fields evaluate to their concrete values, so `evalRV(rrec, E) = Ok(concrete_record)`. □

---

## 6. Main Soundness Theorem

### Theorem 6.1 (Partial Evaluation Soundness)

If:
1. `Γ ⊢ r : τ` (residual `r` is well-typed)
2. `E ≼_Γ PE` (concrete store refines partial store)

Then:
```
⟦r⟧ᵣ_E ≃ ⟦pe(r, PE)⟧ᵣ_E
```

where `≃` means: both sides are `Ok(v)` for the same `v`, or both sides are errors (possibly different error types).

*Proof.* By structural induction on `r`.

---

**Case `r = val(rv, τ)` [PE-Val]:**

`pe(val(rv, τ), PE) = val(rv, τ)`.

LHS = `⟦val(rv, τ)⟧ᵣ_E = evalRV(rv, E)`.
RHS = `⟦val(rv, τ)⟧ᵣ_E = evalRV(rv, E)`.

LHS = RHS. □

---

**Case `r = error(τ)` [PE-Err]:**

`pe(error(τ), PE) = error(τ)`.

Both sides evaluate to `Error`. □

---

**Case `r = r₁ && r₂ : τ` [PE-And]:**

Let `r₁' = pe(r₁, PE)` and `r₂' = pe(r₂, PE)`.

By induction: `⟦r₁⟧ᵣ_E ≃ ⟦r₁'⟧ᵣ_E` and `⟦r₂⟧ᵣ_E ≃ ⟦r₂'⟧ᵣ_E`.

**Sub-case [PE-And-T]:** `r₁' = val(true, _)`.

`pe(r, PE) = r₂'`.

LHS: `⟦r₁ && r₂⟧ᵣ_E = let b₁ = ⟦r₁⟧ᵣ_E as Bool in if ¬b₁ then false else ⟦r₂⟧ᵣ_E as Bool`.

Since `⟦r₁⟧ᵣ_E ≃ ⟦r₁'⟧ᵣ_E = Ok(true)`, we have `⟦r₁⟧ᵣ_E = Ok(true)` (by ≃ on Ok values).
So LHS = `⟦r₂⟧ᵣ_E as Bool`.

RHS: `⟦r₂'⟧ᵣ_E`.

By IH, `⟦r₂⟧ᵣ_E ≃ ⟦r₂'⟧ᵣ_E`. Since both sides are passed through `as Bool`, and ≃ preserves Ok values, LHS ≃ RHS. □

**Sub-case [PE-And-F]:** `r₁' = val(false, _)`.

`pe(r, PE) = val(false, τ)`.

By IH, `⟦r₁⟧ᵣ_E = Ok(false)`. So LHS = `Ok(false)`. RHS = `Ok(false)`. □

**Sub-case [PE-And-Err]:** `r₁' = error(_)`.

`pe(r, PE) = error(τ)`.

By IH, `⟦r₁⟧ᵣ_E` is an error. So LHS is an error. RHS is an error. LHS ≃ RHS. □

**Sub-case [PE-And-RF]:** `r₂' = val(false, _)` and `errorFree(r₁')`.

`pe(r, PE) = val(false, τ)`.

By IH, `⟦r₂⟧ᵣ_E = Ok(false)`. So regardless of `⟦r₁⟧ᵣ_E`:
- If `⟦r₁⟧ᵣ_E = Ok(true)`: LHS = `Ok(false)` (from r₂). RHS = `Ok(false)`. ✓
- If `⟦r₁⟧ᵣ_E = Ok(false)`: LHS = `Ok(false)` (short-circuit). RHS = `Ok(false)`. ✓
- If `⟦r₁⟧ᵣ_E = Error`: But `errorFree(r₁')` and IH imply `⟦r₁'⟧ᵣ_E` is Ok (by Lemma 6.2 below), so `⟦r₁⟧ᵣ_E` is Ok. Contradiction. ✓

**Sub-case [PE-And-Res]:** `pe(r, PE) = r₁' && r₂' : τ`.

LHS = `let b₁ = ⟦r₁⟧ᵣ_E as Bool in ...`.
RHS = `let b₁ = ⟦r₁'⟧ᵣ_E as Bool in ...`.

By IH on both sub-expressions, LHS ≃ RHS. □

---

**Case `r = r₀ has a : τ` [PE-Has]:**

Let `r₀' = pe(r₀, PE)`. By IH: `⟦r₀⟧ᵣ_E ≃ ⟦r₀'⟧ᵣ_E`.

**Sub-case [PE-Has-Err]:** `r₀' = error(_)`.

Both sides error. □

**Sub-case [PE-Has-Rec], `rrec.find(a) = present(_)`:**

`pe(r, PE) = val(true, τ)`.

Since `r₀'` is a record value, `⟦r₀'⟧ᵣ_E = evalRV(rrec, E)`. If this succeeds (producing concrete record `rec`), then `a ∈ dom(rec)` (the present entry evaluates to a value at key `a`).

By IH, `⟦r₀⟧ᵣ_E` also produces a record containing `a`. So `hasAttr(⟦r₀⟧ᵣ_E, a, E) = Ok(true)`.

LHS = `Ok(true)`. RHS = `Ok(true)`. □

**Sub-case [PE-Has-Rec], `rrec.find(a) = unknown(tgt, _)`:**

`pe(r, PE) = tgt has a : τ`.

LHS: `hasAttr(⟦r₀⟧ᵣ_E, a, E)`.
RHS: `hasAttr(⟦tgt⟧ᵣ_E, a, E)`.

The target `tgt` was stored when the record was created by `toRV`. By Lemma 5.1, `⟦tgt⟧ᵣ_E = Ok(v_container)` where `v_container` is the entity/record that contains the field `a`.

Since the unknown entry exists (by Lemma 4.3, the concrete attribute exists), `hasAttr(v_container, a, E) = Ok(true)`.

Meanwhile, `⟦r₀⟧ᵣ_E` evaluates to the concrete record, which also contains `a`. So LHS = `Ok(true)`.

Both sides = `Ok(true)`. □

**Sub-case [PE-Has-Rec], `rrec.find(a) = ⊥`:**

`pe(r, PE) = val(false, τ)`.

By Lemma 4.1 (adapted to records), `a ∉ dom(concrete_record)`. So `hasAttr` returns `false`.

LHS = `Ok(false)`. RHS = `Ok(false)`. □

**Sub-case [PE-Has-Ent], `attrs.find(a) = present(_)`:**

`pe(r, PE) = val(true, τ)`.

By Lemma 4.2, `a ∈ dom(E(uid))`. So `hasAttr(uid, a, E) = Ok(true)`.

By IH, `⟦r₀⟧ᵣ_E = Ok(uid)`. So LHS = `Ok(true)`. RHS = `Ok(true)`. □

**Sub-case [PE-Has-Ent], `attrs.find(a) = unknown(_)`:**

`pe(r, PE) = r₀' has a : τ` where `r₀' = val(uid, _)`.

LHS: `hasAttr(⟦r₀⟧ᵣ_E, a, E)`.
RHS: `hasAttr(⟦r₀'⟧ᵣ_E, a, E) = hasAttr(uid, a, E)`.

By IH, `⟦r₀⟧ᵣ_E ≃ ⟦r₀'⟧ᵣ_E = Ok(uid)`. So `⟦r₀⟧ᵣ_E = Ok(uid)`.

LHS = `hasAttr(uid, a, E)` = RHS. □

**Sub-case [PE-Has-Ent], `attrs.find(a) = ⊥`:**

`pe(r, PE) = val(false, τ)`.

By Lemma 4.1, `a ∉ dom(E(uid))`. So `hasAttr(uid, a, E) = a ∈ dom(attrsOrEmpty(uid, E))`.

If `uid ∈ dom(E)`: `attrsOrEmpty(uid, E) = E(uid)`, and `a ∉ dom(E(uid))`, so result is `false`. ✓
If `uid ∉ dom(E)`: But `uid ∈ dom(PE)` (we found attrs), so by refinement `uid ∈ dom(E)`. Contradiction.

LHS = `Ok(false)`. RHS = `Ok(false)`. □

**Sub-case [PE-Has-Ent], `PE.attrs(uid) = None`:**

`pe(r, PE) = r₀' has a : τ`.

RHS: `hasAttr(⟦r₀'⟧ᵣ_E, a, E)`. By IH, `⟦r₀⟧ᵣ_E ≃ ⟦r₀'⟧ᵣ_E`.

LHS = `hasAttr(⟦r₀⟧ᵣ_E, a, E)` ≃ `hasAttr(⟦r₀'⟧ᵣ_E, a, E)` = RHS. □

**Sub-case [PE-Has-Unk]:** `r₀'` is not a value.

`pe(r, PE) = r₀' has a : τ`.

RHS: `hasAttr(⟦r₀'⟧ᵣ_E, a, E)`. By IH, LHS ≃ RHS. □

---

**Case `r = r₀.a : τ` [PE-Get]:**

Let `r₀' = pe(r₀, PE)`. By IH: `⟦r₀⟧ᵣ_E ≃ ⟦r₀'⟧ᵣ_E`.

**Sub-case [PE-Get-Err]:** Both sides error. □

**Sub-case [PE-Get-Rec], `rrec.find(a) = present(rv)`:**

`pe(r, PE) = val(rv, τ)`.

LHS: `getAttr(⟦r₀⟧ᵣ_E, a, E)`.
RHS: `evalRV(rv, E)`.

By IH, `⟦r₀⟧ᵣ_E ≃ ⟦r₀'⟧ᵣ_E = evalRV(rrec, E)`. If this succeeds, the concrete record has `a` mapped to the value that `rv` evaluates to. So `getAttr(concrete_record, a, E) = evalRV(rv, E)`.

LHS ≃ RHS. □

**Sub-case [PE-Get-Rec], `rrec.find(a) = unknown(tgt, _)`:**

`pe(r, PE) = tgt.a : τ`.

LHS: `getAttr(⟦r₀⟧ᵣ_E, a, E)`.
RHS: `getAttr(⟦tgt⟧ᵣ_E, a, E)`.

By target correctness (Lemma 5.1), `⟦tgt⟧ᵣ_E = Ok(v_container)`. The concrete value at `a` in `v_container` is the same as the concrete value at `a` in the record that `r₀` evaluates to (because the target points to the entity that owns this record, and `getAttr` on the entity retrieves the same field).

More precisely: the record `rrec` was produced by `toRV(tgt, pv, τ)` during a previous `pe` step where `getAttr` on entity `uid` found a present partial value `pv`. The target `tgt` is the entity residual `val(uid, _)`. So `⟦tgt⟧ᵣ_E = Ok(uid)`, and `getAttr(uid, a, E) = E(uid).a`.

Meanwhile, `⟦r₀⟧ᵣ_E` evaluates to a concrete record that was derived from `E(uid)`. The field `a` in this record is `E(uid).a` (accessed through the record) or `E(uid).a` (accessed through the entity). Same value.

LHS ≃ RHS. □

**Sub-case [PE-Get-Ent], `attrs.find(a) = present(pv)`:**

`pe(r, PE) = val(toRV(r₀', pv, τ), τ)`.

LHS: `getAttr(uid, a, E) = Ok(E(uid).a)`.
RHS: `evalRV(toRV(r₀', pv, τ), E)`.

By Lemma 4.2, `E, Γ ⊢ E(uid).a ≼ pv`. The target for `toRV` is `r₀' = val(uid, _)`, so `⟦r₀'⟧ᵣ_E = Ok(uid)`.

By Lemma 5.3, `evalRV(toRV(r₀', pv, τ), E) = Ok(E(uid).a)`.

LHS = RHS. □

**Sub-case [PE-Get-Ent], `attrs.find(a) = unknown(_)`:**

`pe(r, PE) = r₀'.a : τ`.

LHS: `getAttr(⟦r₀⟧ᵣ_E, a, E)`.
RHS: `getAttr(⟦r₀'⟧ᵣ_E, a, E)`.

By IH, `⟦r₀⟧ᵣ_E ≃ ⟦r₀'⟧ᵣ_E`. So LHS ≃ RHS. □

**Remaining sub-cases** (`find = ⊥`, `attrs = None`, non-value receiver): All produce residuals of the form `r₀'.a : τ`, and soundness follows directly from the IH. □

---

### Lemma 6.2 (Error-free residuals evaluate successfully)

If `Γ ⊢ r : τ` and `errorFree(r)` and `E` is well-typed w.r.t. `Γ`, then `⟦r⟧ᵣ_E` is `Ok(v)` for some `v`.

*Proof sketch.* By induction on `r`. Values always succeed (for our simplified language without arithmetic). Variables don't exist in our language. `hasAttr` never errors. `getAttr` could error, but `getAttr` is not `errorFree` in general (it's not in our `errorFree` definition since we don't have it — in the full Cedar, `getAttr` can error for missing entities, but in our simplified language with only well-typed expressions, `getAttr` on a well-typed entity always succeeds). For `&&`, both sub-expressions are error-free by definition, so by IH both succeed, and `&&` on booleans succeeds. □

---

This completes the proof of Theorem 6.1. ∎
