import Mathlib

open Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Topology

/- English proof (translation)
Introduce `X _ _ _ A B hA hB`. Establish `h : ((A ⊔ B : AddSubgroup X) : Set X) = (A : Set X) + (B : Set X)`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]`. Rewrite using `[h]`.

Conclude with `hA.add hB`.
-/
theorem isCompact_addSubgroup_sup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  intro X _ _ _ A B hA hB
  have h : ((A ⊔ B : AddSubgroup X) : Set X) = (A : Set X) + (B : Set X) := by
    ext x
    simp only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]
  rw [h]
  exact hA.add hB

end GlobalTheory.CompanionTheory.Topology
