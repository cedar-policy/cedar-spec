# Style guidelines for Cedar Lean

The Cedar Lean formalization uses the following coding conventions, adapted from [Lean 4](https://leanprover.github.io/lean4/doc/lean3changes.html#style-changes) and [Mathlib 4](https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki#naming-convention).

## Imports

Sort `import` and `open` statements lexicographically. Keep imports to a minimum.

## Casing

* Type variables are lower-case Greek letters.
* Theorem names and `Prop` terms are in `lower_snake_case`.
* Inductive types, structures, typeclasses, modules, and namespaces use `UpperCamelCase`.
* Constructors of inductive types use `lowerCamelCase`.
* Function names are `lowerCamelCase` unless they return a `Prop`, in which case they are `UpperCamelCase`.
* Everything else (e.g., structure fields and local variables) is `lowerCamelCase`.

## Indentation

Declaration and theorem bodies should always be indented:

```
inductive Hello where
  | world
  | planet

structure Point where
  x : Nat
  y : Nat

def Point.addX : Point → Point → Nat :=
  fun { x := a, .. } { x := b, .. } => a + b
```

In structures and typeclass definitions, prefer `where` to `:=`.

## Theorem statements

Indent long theorem statements.

Minimize the use of explicitly named hypotheses, and use implications instead.

For example, prefer anonymous hypotheses, like this:
```
theorem even_is_not_odd (n : Nat) : Even n -> ¬ Odd n
:= by ...
```

Over named hypotheses, like this:

```
theorem even_is_not_odd (n : Nat) (isEven : Even n) : ¬ Odd n
:= by ...
```

To break up implications across multiple lines:
* If there is only one hypothesis (e.g., `A -> B`), put the implication symbol at the end of the first line (e.g., `A ->\n B`).
* Otherwise, put the implication symbol at the start of the subsequent lines (e.g., `A \n-> B \n-> C`).

## Comments

Main theorems should have a docstring comment `/-- ... -/` explaining what is proven. See [here](https://leanprover-community.github.io/contribute/doc.html) for more information on the Mathlib documentation style.


## Proof stability
To make version upgrades easier, strive to follow these guidelines:

- Use `simp only` or `csimp` instead of `simp`. As an exception to this, it's
    okay to use `simp` to close a goal (but if `csimp` works, you're still
    encouraged to use that instead).
- Use `have` or `replace` to deconstruct values. Use `rcases` only to split
    disjunctions.
- Use `exact` instead of `apply` or `assumption` whenever possible.
- Fully spell out types in function and theorem declarations.
