# Paper Proof Part 4: Type Preservation and Batched Evaluation

## 7. Type Preservation

### Theorem 7.1 (Partial evaluation preserves well-typedness)

If `Γ ⊢ r : τ` and `E ≼_Γ PE`, then `Γ ⊢ pe(r, PE) : τ'` where `τ' = τ` (same type).

*Proof.* By structural induction on `r`.

**Case `val(rv, τ)`:** `pe` returns `val(rv, τ)`. Type unchanged. □

**Case `error(τ)`:** `pe` returns `error(τ)`. Type unchanged. □

**Case `r₁ && r₂ : Bool`:**

- [PE-And-T]: returns `r₂'`. By IH, `Γ ⊢ r₂' : Bool`. □
- [PE-And-F]: returns `val(false, Bool)`. Well-typed. □
- [PE-And-Err]: returns `error(Bool)`. Well-typed. □
- [PE-And-RF]: returns `val(false, Bool)`. Well-typed. □
- [PE-And-Res]: returns `r₁' && r₂' : Bool`. By IH both sub-residuals are well-typed at `Bool`. □

**Case `r₀ has a : Bool`:**

All branches return either `val(true/false, Bool)`, `error(Bool)`, or `r' has a : Bool`. The type is always `Bool`. By IH, `r'` is well-typed, so the `hasAttr` residual is well-typed. □

**Case `r₀.a : τ`:**

- [PE-Get-Rec], present: returns `val(rv, τ)`. Need `rv` well-typed at `τ`. Since the record is well-typed and `rv` is the value at attribute `a` whose type in the record type is `τ`, this holds. □
- [PE-Get-Ent], present: returns `val(toRV(r₀', pv, τ), τ)`. Need `toRV(r₀', pv, τ)` well-typed. By Lemma 7.2 below. □
- All residual cases: return `r'.a : τ` or `tgt.a : τ`. The type annotation is `τ`, and the sub-expression is well-typed by IH or by target well-typedness (Lemma 7.3). □

### Lemma 7.2 (toRV preserves well-typedness)

If `Γ ⊢ tgt : τ_tgt` and `pv` is well-typed at `τ` w.r.t. `Γ`, then `toRV(tgt, pv, τ)` is a well-typed residual value at `τ`.

*Proof.* By induction on `pv`. For records, each present field recurses with a well-typed target (`tgt.a` is well-typed if `tgt` is well-typed and `a` is a valid attribute). Each unknown field stores `tgt` which is well-typed by hypothesis. □

### Lemma 7.3 (Targets are well-typed)

Every target expression stored in an `unknown(tgt, τ)` within a residual produced by `pe` is well-typed.

*Proof.* Targets are created in [PE-Get-Ent] as `r₀'` (the partially-evaluated receiver) or in `toRV` as `tgt.a`. In both cases, the target is well-typed by IH or by Lemma 7.2. □

---

## 8. Batched Evaluation

### 8.1 Setup

An **entity loader** `L : Set(UID) → Map(UID, Option(EntityData))` fetches entities from a backing store. `L(S)(uid) = None` means the entity doesn't exist.

**Missing entity conversion:**
```
asPartial(None)    = { attrs: Some({}) }     -- empty, not unknown
asPartial(Some(d)) = d.asPartial             -- standard conversion
```

**Well-behaved loader:**
```
WellBehaved(E, L) ≡ ∀S. S ⊆ dom(L(S)) ∧ E ≼_Γ (L(S).map(asPartial))
```

### 8.2 The Batched Evaluation Loop

```
batchLoop(r, E_concrete, L, store, 0) = r
batchLoop(r, E_concrete, L, store, n+1) =
  let toLoad = literalUIDs(r) \ dom(store)
  let newData = L(toLoad).map(asPartial)
  let store' = newData ∪ store
  let r' = pe(r, store')
  match r' with
  | val(rv, τ) → val(rv, τ)
  | _          → batchLoop(r', E_concrete, L, store', n)
```

### 8.3 Store Monotonicity

**Lemma 8.1.** If `E ≼_Γ store₁` and `E ≼_Γ store₂`, then `E ≼_Γ (store₂ ∪ store₁)`.

*Proof.* For any `uid ∈ dom(store₂ ∪ store₁)`: if `uid ∈ dom(store₂)`, use the refinement from `store₂`; otherwise `uid ∈ dom(store₁)`, use that refinement. Both are valid since both refine `E`. □

### 8.4 Missing Entity Equivalence

**Lemma 8.2.** For any expression `r` and entity `uid`:
```
⟦r⟧ᵣ_E  where uid ∉ dom(E)
```
produces the same result as
```
⟦r⟧ᵣ_{E ∪ {uid ↦ {attrs:{}, ancestors:∅}}}
```

*Proof sketch.* In our simplified language:
- `getAttr(uid, a, E)` errors if `uid ∉ dom(E)`. With the empty entity, `getAttr(uid, a, E')` also errors (attribute not found in empty record). Same error behavior.
- `hasAttr(uid, a, E)` returns `a ∈ dom(attrsOrEmpty(uid, E)) = a ∈ dom({}) = false`. With the empty entity, same result.

So the observable behavior is identical. □

This justifies `asPartial(None) = { attrs: Some({}) }` — converting missing entities to empty entities rather than leaving them as unknown.

### Theorem 8.3 (Batched Evaluation Soundness)

If `Γ ⊢ r : τ` and `WellBehaved(E, L)`, then:
```
⟦batchLoop(r, E, L, ∅, n)⟧ᵣ_E ≃ ⟦r⟧ᵣ_E
```

*Proof.* By induction on `n`.

**Base case `n = 0`:** `batchLoop` returns `r`. Trivially `⟦r⟧ᵣ_E ≃ ⟦r⟧ᵣ_E`. □

**Inductive case `n+1`:**

Let `store' = newData ∪ store` and `r' = pe(r, store')`.

By `WellBehaved`, `E ≼_Γ newData`. By the outer induction hypothesis (on the accumulated store), `E ≼_Γ store`. By Lemma 8.1, `E ≼_Γ store'`.

By Theorem 6.1 (soundness of `pe`): `⟦r⟧ᵣ_E ≃ ⟦r'⟧ᵣ_E`.

If `r' = val(rv, τ)`: `batchLoop` returns `val(rv, τ)`. So `⟦batchLoop(...)⟧ᵣ_E = ⟦val(rv, τ)⟧ᵣ_E = ⟦r'⟧ᵣ_E ≃ ⟦r⟧ᵣ_E`. □

Otherwise: `batchLoop` recurses with `r'`, `store'`, `n`.

By Theorem 7.1, `Γ ⊢ r' : τ` (type preserved).

By IH on `n`: `⟦batchLoop(r', E, L, store', n)⟧ᵣ_E ≃ ⟦r'⟧ᵣ_E`.

Chaining: `⟦batchLoop(r', E, L, store', n)⟧ᵣ_E ≃ ⟦r'⟧ᵣ_E ≃ ⟦r⟧ᵣ_E`. □

---

## 9. Proof Structure Preview

The full proof dependency graph and theorem index are in [Part 5, §15](07-paper-proof-part5.md#15-summary). The remaining pieces — conversion soundness, policy-level soundness, and authorization-level soundness — are also developed there.
