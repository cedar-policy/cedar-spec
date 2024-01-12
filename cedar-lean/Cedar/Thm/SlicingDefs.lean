import Cedar.Spec

namespace Cedar.Thm

open Cedar.Spec

/--
A policy slice is a subset of a collection of policies.  This slice is sound for
a given request and entities if every policy in the collection that is not in
the slice is also not satisfied with respect to the request and entities, and
doesn't produce an error when evaluated.
-/
def IsSoundPolicySlice (req : Request) (entities : Entities) (slice policies : Policies) : Prop :=
  slice ⊆ policies ∧
  ∀ policy ∈ policies,
    policy ∉ slice →
    ¬ satisfied policy req entities ∧ ¬ hasError policy req entities


end Cedar.Thm
