module

public import Cedar.Spec
public import Cedar.Data
public import Cedar.Thm.Data.Map
public import Cedar.Thm.Data.MapUnion
public import Cedar.Thm.Validation.Slice.Reachable
public import Cedar.Thm.Validation.Levels.ReachableChild

@[expose] public section

namespace Cedar.Thm

open Cedar.Data Cedar.Spec Cedar.Validation

/-- If `next` is found in record `r` at key `a`, then sliceEUIDs of `next` ⊆ sliceEUIDs of record. -/
theorem sliceEUIDs_record_field {r : Map Attr Value} {a : Attr} {next : Value}
    (hfind : r.find? a = some next) :
    ∀ uid, uid ∈ Value.sliceEUIDs next → uid ∈ Value.sliceEUIDs (.record r) := by
  intro uid hmem
  rw [mem_sliceEUIDs_record]
  exact ⟨(a, next), Map.find?_mem_toList hfind, hmem⟩

/-- If `next` is found in entity data attrs at key `a`, then sliceEUIDs of `next` ⊆ entity's sliceEUIDs. -/
theorem sliceEUIDs_entity_attr {ed : EntityData} {a : Attr} {next : Value}
    (hfind : ed.attrs.find? a = some next) :
    ∀ uid, uid ∈ Value.sliceEUIDs next → uid ∈ ed.sliceEUIDs := by
  intro uid hmem
  have hval : next ∈ ed.attrs.values := Map.find?_some_implies_in_values hfind
  exact mem_sliceEUIDs_entityData.mpr (.inl ⟨next, hval, hmem⟩)

end Cedar.Thm
