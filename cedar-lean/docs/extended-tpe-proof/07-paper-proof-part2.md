# Paper Proof Part 2: Partial Evaluation and Refinement

## 3. The Partial Evaluator

`pe(r, PE) : Residual` — partially evaluates a residual given a partial entity store.

### 3.1 Core Rules

```
pe(val(rv, τ), PE)        = val(rv, τ)                    [PE-Val]
pe(error(τ), PE)          = error(τ)                       [PE-Err]
```

### 3.2 And (short-circuit)

```
pe(r₁ && r₂ : τ, PE) =
  let r₁' = pe(r₁, PE), r₂' = pe(r₂, PE) in
  match r₁' with
  | val(true, _)   → r₂'                                  [PE-And-T]
  | val(false, _)  → val(false, τ)                         [PE-And-F]
  | error(_)       → error(τ)                              [PE-And-Err]
  | _              → match r₂' with
                     | val(false, _) →
                         if errorFree(r₁') then val(false, τ)  [PE-And-RF]
                         else r₁' && r₂' : τ
                     | _ → r₁' && r₂' : τ                 [PE-And-Res]
```

### 3.3 HasAttr

```
pe(r has a : τ, PE) =
  let r' = pe(r, PE) in
  match r' with
  | error(_) → error(τ)                                    [PE-Has-Err]

  | val(rrec, _) →                                         [PE-Has-Rec]
      match rrec.find(a) with
      | present(_)       → val(true, τ)
      | unknown(tgt, _)  → tgt has a : τ                   ← delegates to TARGET
      | ⊥                → val(false, τ)

  | val(uid, _) →                                          [PE-Has-Ent]
      match PE.attrs(uid) with
      | Some(attrs) →
          match attrs.find(a) with
          | present(_)  → val(true, τ)
          | unknown(_)  → r' has a : τ                     ← delegates to SELF
          | ⊥           → val(false, τ)
      | None → r' has a : τ

  | _ → r' has a : τ                                       [PE-Has-Unk]
```

### 3.4 GetAttr

```
pe(r.a : τ, PE) =
  let r' = pe(r, PE) in
  match r' with
  | error(_) → error(τ)                                    [PE-Get-Err]

  | val(rrec, _) →                                         [PE-Get-Rec]
      match rrec.find(a) with
      | present(rv) → val(rv, τ)
      | unknown(tgt, _) → tgt.a : τ                        ← delegates to TARGET
      | ⊥ → r'.a : τ

  | val(uid, _) →                                          [PE-Get-Ent]
      match PE.attrs(uid) with
      | Some(attrs) →
          match attrs.find(a) with
          | present(pv) → val(toRV(r', pv, τ), τ)          ← creates targets
          | unknown(_)  → r'.a : τ                          ← delegates to SELF
          | ⊥           → r'.a : τ
      | None → r'.a : τ

  | _ → r'.a : τ                                           [PE-Get-Unk]
```

---

## 4. Refinement

### 4.1 Value Refinement

`E, Γ ⊢ v ≼ pv` — concrete value `v` refines partial value `pv`.

```
─────────────────── [Ref-Bool]
E, Γ ⊢ b ≼ b

─────────────────── [Ref-UID]
E, Γ ⊢ uid ≼ uid

∀(aᵢ, present(pvᵢ)) ∈ prec : E, Γ ⊢ vᵢ ≼ pvᵢ
∀(aᵢ, unknown(τᵢ)) ∈ prec  : E, Γ ⊢ vᵢ : τᵢ
∀(aᵢ, vᵢ) ∈ rec : ∃pa. (aᵢ, pa) ∈ prec
──────────────────────────────────────────────── [Ref-Rec]
E, Γ ⊢ {a₁:v₁,...} ≼ {a₁:pa₁,...}
```

The third premise of [Ref-Rec] is crucial: every concrete attribute must have a corresponding partial entry. This ensures that `find(a) = ⊥` in the partial record implies `a ∉ dom(concrete_record)`.

### 4.2 Entity Store Refinement

`E ≼_Γ PE` — concrete store `E` refines partial store `PE`.

```
∀ uid ∈ dom(PE):
  uid ∈ dom(E) ∧
  PE(uid).attrs = None  ∨
  PE(uid).attrs = Some(pattrs) ∧ E, Γ ⊢ E(uid) ≼ pattrs
──────────────────────────────────────────────────────────── [Ref-Store]
E ≼_Γ PE
```

### 4.3 Key Consequences of Refinement

**Lemma 4.1 (Absent attribute implies concrete absence).**
If `E ≼_Γ PE` and `PE.attrs(uid) = Some(attrs)` and `attrs.find(a) = ⊥`, then `a ∉ dom(E(uid))`.

*Proof.* By [Ref-Store], `E, Γ ⊢ E(uid) ≼ attrs`. By the third premise of [Ref-Rec], every concrete attribute has a partial entry. Contrapositive: if `a` has no partial entry, `a` is not a concrete attribute. □

**Lemma 4.2 (Present attribute matches).**
If `E ≼_Γ PE` and `PE.attrs(uid) = Some(attrs)` and `attrs.find(a) = present(pv)`, then `E(uid).a` exists and `E, Γ ⊢ E(uid).a ≼ pv`.

*Proof.* By [Ref-Store] and [Ref-Rec], the present entry corresponds to a concrete attribute with a refining value. □

**Lemma 4.3 (Unknown attribute exists and is well-typed).**
If `E ≼_Γ PE` and `PE.attrs(uid) = Some(attrs)` and `attrs.find(a) = unknown(τ)`, then `E(uid).a` exists and `Γ ⊢ E(uid).a : τ`.

*Proof.* By [Ref-Store] and the second premise of [Ref-Rec]. □
