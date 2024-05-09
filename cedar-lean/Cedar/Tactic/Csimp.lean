/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Data.Set
import Cedar.Spec.Value
import Cedar.Thm.Data.Control

namespace Cedar.Tactic
open Lean Parser

/--
`csimp` is a version of `simp` that uses a different set of lemmas.
It exists to avoid the potential breakage when upgrading Lean versions if the
set of `simp` lemmas changes (because we control the set of lemmas used here,
and it is stable across Lean versions unless we choose to make changes).
It is also an alternative to the Mathlib convention of using `simp only`
everywhere, which is a hassle and clutters proofs.

The set of `csimp` lemmas is intended to be a subset of the `simp` lemmas, so
(among other things) `csimp` should have intermediate performance between `simp`
and a dedicated `simp only`.

`csimp` supports `at` syntax, e.g., all of the following are valid:
* `csimp`
* `csimp at h`
* `csimp at *`

but `csimp` does not support extending the lemmas inline, e.g.,
* `csimp [h₂]` (instead, use `csimp ; simp only [h₂]`, or the other order)

only because I couldn't get that to work. If you can get it to work,
contributions welcome.
-/
syntax (name := csimp) "csimp" (Tactic.config)? (ppSpace Tactic.location)? : tactic

macro_rules
  | `(tactic| csimp $(config)? $(loc)?) =>
      `(tactic| simp $(config)? only [
          and_false,
          and_true,
          false_and,
          true_and,
          or_false,
          or_true,
          false_or,
          true_or,

          not_and,
          not_false_eq_true,
          not_true_eq_false,
          decide_eq_true_eq,

          ne_eq,
          id_eq,

          ite_not,
          ite_true,
          ite_false,

          false_implies,
          implies_true,
          imp_self,
          and_imp,

          gt_iff_lt,

          beq_eq_false_iff_ne,
          beq_iff_eq,
          bne_iff_ne,

          forall_const,
          forall_eq',
          forall_eq_or_imp,
          forall_exists_index,
          forall_apply_eq_imp_iff₂,

          exists_false,
          exists_const,
          exists_eq',
          exists_eq_left',
          exists_eq_right,
          exists_eq_right_right,
          exists_and_right,
          exists_eq_or_imp,

          Bool.and_eq_true,
          Bool.or_eq_true,
          Bool.not_eq_true',
          Bool.not_eq_false,
          Bool.true_or,
          Bool.false_or,

          List.empty_eq,
          List.subset_def,
          List.cons_subset,
          List.not_mem_nil,
          List.mem_cons,
          List.mem_map,
          List.mem_filterMap,
          List.map_nil,
          List.map_cons,
          List.map_map,
          List.any_nil,
          List.any_cons,
          List.any_eq_true,
          List.all_nil,
          List.all_cons,
          List.all_eq_true,
          List.find?_nil,
          List.find?_cons,
          List.mapM'_nil,
          List.mapM'_cons,
          List.mapM_nil,
          List.mapM_cons,
          List.filter_nil,
          List.filter_cons,
          List.filterMap_nil,
          List.filterMap_cons,
          List.foldlM_nil,
          List.foldlM_cons,

          Option.none_bind,
          Option.some_bind,
          Option.isSome_none,
          Option.isSome_some,
          Option.bind_eq_none,
          Option.bind_eq_some,
          Option.map_none',
          Option.map_some',

          -- the theorems from Cedar.Thm.Data.Control
          Except.bind_ok_T,
          Except.bind_ok,
          Except.bind_err,
          Option.bind_some_T,
          Option.bind_some_fun,
          Option.bind_none_fun,

          -- some Spec definitions which we want to eagerly expand
          Cedar.Spec.Result.as,
          Cedar.Spec.Value.asBool,

          -- `injEq` for a bunch of different types
          Option.some.injEq,
          List.cons.injEq,
          Prod.mk.injEq,
          Except.ok.injEq,
          Except.error.injEq,
          Cedar.Data.Set.mk.injEq,
          Cedar.Data.Map.mk.injEq,
          Cedar.Spec.Prim.entityUID.injEq,
          Cedar.Spec.Value.prim.injEq,
          Cedar.Spec.Value.record.injEq,
          Cedar.Spec.Prim.bool.injEq,

          -- some Lean definitions which we want to eagerly expand
          Coe.coe,
          pure,
          Option.pure_def,
          Option.bind_eq_bind,
          Except.pure,
        ]
        $(loc)?
      )
