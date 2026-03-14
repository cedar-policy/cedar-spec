# Paper Proof: Extended TPE Correctness (Simplified Cedar)

## Part 1: Language Definition and Concrete Semantics

### 1.1 Syntax

We work with a simplified Cedar with three expression forms and three value forms.

**Values:**
```
v ::= b                     (boolean, b ∈ {true, false})
    | uid                   (entity UID)
    | { a₁: v₁, ..., aₙ: vₙ }  (record)
```

**Expressions:**
```
e ::= v                     (literal value)
    | e.a                   (getAttr)
    | e has a               (hasAttr)
    | e₁ && e₂             (short-circuit and)
```

**Entity store** `E` maps entity UIDs to records: `E : UID → Record`.

### 1.2 Concrete Evaluation

`⟦e⟧_E : Value + Error`

```
⟦v⟧_E                    = v
⟦e.a⟧_E                  = let v = ⟦e⟧_E in getAttr(v, a, E)
⟦e has a⟧_E              = let v = ⟦e⟧_E in hasAttr(v, a, E)
⟦e₁ && e₂⟧_E            = let b₁ = ⟦e₁⟧_E as Bool in
                            if ¬b₁ then false else ⟦e₂⟧_E as Bool
```

Where:
```
getAttr(uid, a, E)        = E(uid).a          (error if uid ∉ dom(E) or a ∉ dom(E(uid)))
getAttr({...aᵢ:vᵢ...}, a, E) = vᵢ            (where aᵢ = a; error if a ∉ record)
hasAttr(uid, a, E)        = a ∈ dom(attrsOrEmpty(uid, E))
hasAttr({...}, a, E)      = a ∈ dom(record)
attrsOrEmpty(uid, E)      = E(uid) if uid ∈ dom(E), else {}
```

Note: `hasAttr` on entities uses `attrsOrEmpty` (never errors), while `getAttr` on entities uses `E.attrs` (errors if entity missing). This asymmetry is faithful to Cedar.

---

### 1.3 Types

```
τ ::= Bool | Entity(ety) | Record(rty)
rty : Attr → Qualified(τ)     (maps attribute names to qualified types)
```

**Well-typed values:** `E, Γ ⊢ v : τ` (standard).

**Well-typed expressions:** `Γ ⊢ e : τ` where Γ is a type environment containing entity schema.

---

## Part 2: Partial Inputs and Residuals

### 2.1 Partial Values

```
pv ::= b | uid | prec
prec = { a₁: pa₁, ..., aₙ: paₙ }
pa ::= present(pv) | unknown(τ)
```

**Partial entity store** `PE` maps UIDs to partial entity data:
```
PE : UID ⇀ PEntityData
PEntityData = { attrs: Option(Map(Attr, PA)) }
```

Where `PE(uid) = ⊥` means the entity is not in the partial store, and `PE(uid).attrs = None` means the entity is present but its attributes are entirely unknown.

### 2.2 Residuals

```
r ::= val(rv, τ)           (residual value with type)
    | r.a : τ              (residual getAttr)
    | r has a : τ          (residual hasAttr)
    | r₁ && r₂ : τ        (residual and)
    | error(τ)             (error)

rv ::= b | uid | rrec
rrec = { a₁: ra₁, ..., aₙ: raₙ }
ra ::= present(rv) | unknown(target: r, τ)
```

The key extension: `unknown(target, τ)` stores a **target** residual expression.

### 2.3 Residual Evaluation (Semantics of Residuals)

`⟦r⟧ᵣ_E : Value + Error` — evaluates a residual against a concrete entity store.

```
⟦val(rv, τ)⟧ᵣ_E         = evalRV(rv, E)
⟦r.a : τ⟧ᵣ_E            = let v = ⟦r⟧ᵣ_E in getAttr(v, a, E)
⟦r has a : τ⟧ᵣ_E        = let v = ⟦r⟧ᵣ_E in hasAttr(v, a, E)
⟦r₁ && r₂ : τ⟧ᵣ_E      = let b₁ = ⟦r₁⟧ᵣ_E as Bool in
                            if ¬b₁ then false else ⟦r₂⟧ᵣ_E as Bool
⟦error(τ)⟧ᵣ_E           = Error
```

```
evalRV(b, E)              = b
evalRV(uid, E)            = uid
evalRV(rrec, E)           = { aᵢ: evalRA(raᵢ, aᵢ, E) | (aᵢ, raᵢ) ∈ rrec }

evalRA(present(rv), a, E) = evalRV(rv, E)
evalRA(unknown(tgt, τ), a, E) = ⟦tgt.a : τ⟧ᵣ_E
```

The last line is the critical rule: an unknown attribute is evaluated by constructing a `getAttr` on the target and evaluating it.

### 2.4 Target Construction: `toRV`

`toRV(target, pv, τ) : RV` — converts a partial value to a residual value, threading a target expression.

```
toRV(tgt, b, _)           = b
toRV(tgt, uid, _)         = uid
toRV(tgt, prec, Record(rty)) =
  { aᵢ: toRA(tgt, paᵢ, aᵢ, rty) | (aᵢ, paᵢ) ∈ prec }

toRA(tgt, present(pv), a, rty) =
  present(toRV(tgt.a : Record(rty), pv, rty(a)))
toRA(tgt, unknown(τ), a, rty) =
  unknown(tgt, τ)
```

Note the recursive target threading: for present nested values, the new target is `tgt.a : Record(rty)` — a `getAttr` on the current target.
