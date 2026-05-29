import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec


theorem Cst.Ident.toUnreservedString?_eq_toString
    {i : Cst.Ident} {s : String} :
    i.toUnreservedString? = some s →
    s = CstCommon.Ident.toString i := by
  cases i <;> intro h <;> simp [Cst.Ident.toUnreservedString?] at h
  all_goals first | rfl | (rw [← h]; rfl)

/-- If `mapM` over `toUnreservedString?` succeeds, the result equals `map toString`. -/
theorem mapM_toUnreservedString?_eq_map
    {l : List Cst.Ident} {result : List String} :
    l.mapM Cst.Ident.toUnreservedString? = some result →
    result = l.map CstCommon.Ident.toString := by
  induction l generalizing result with
  | nil =>
    intro h
    simp [List.mapM, List.mapM.loop] at h
    simp [← h]
  | cons hd tl ih =>
    intro h
    simp [List.mapM_cons, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, rest, hrest, heq⟩ := h
    simp [List.map, ← heq]
    exact ⟨Cst.Ident.toUnreservedString?_eq_toString hs, ih hrest⟩

/-- `toAName?` produces the same `Spec.Name` the evaluator builds. -/
theorem Cst.Name.toAName?_agrees
    {n : Cst.Name} {an : Spec.Name} :
    n.toAName? = some an →
    an = { id := n.name.toString,
           path := n.path.map CstCommon.Ident.toString } := by
  intro h
  simp [Cst.Name.toAName?, Option.bind_eq_some_iff] at h
  obtain ⟨id, hid, path, hpath, han⟩ := h
  rw [← han]; congr 1
  · exact Cst.Ident.toUnreservedString?_eq_toString hid
  · exact mapM_toUnreservedString?_eq_map hpath

theorem Cst.Name.toVar?_agrees
    {n : Cst.Name} {v : Var} :
    n.toVar? = some v →
    n.path = [] ∧
    match v with
    | .principal => n.name = Cst.Ident.idPrincipal
    | .action    => n.name = Cst.Ident.idAction
    | .resource  => n.name = Cst.Ident.idResource
    | .context   => n.name = Cst.Ident.idContext := by
  intro h
  simp [Cst.Name.toVar?] at h
  obtain ⟨hpath, hname⟩ := h
  refine ⟨hpath, ?_⟩
  cases hn : n.name <;> rw [hn] at hname <;> simp at hname <;>
    cases v <;> simp_all
