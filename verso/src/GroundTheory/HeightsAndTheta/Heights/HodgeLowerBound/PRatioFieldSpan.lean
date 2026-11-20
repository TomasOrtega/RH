import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRatioFieldSpan
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace RatioFieldSpan

variable {F M : Type} [Field F] [Field M] [Algebra F M]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨i, rfl⟩` from `h`. Conclude with `IntermediateField.subset_adjoin F _ ⟨i, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy`. Rewrite using `[add_div]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[Algebra.smul_def, mul_div_assoc]`.

Conclude with `mul_mem (IntermediateField.algebraMap_mem _ a) hx`.
-/
theorem div_mem_adjoin {I : Type} (u : I → M) (v : M) {x : M}
    (hx : x ∈ Submodule.span F (Set.range u)) :
    x / v ∈ IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    exact IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_div]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, mul_div_assoc]
    exact mul_mem (IntermediateField.algebraMap_mem _ a) hx

/- English proof (translation)
Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨j, rfl⟩`. Establish `h1` using `div_mem_adjoin (F := F) u v (hw j)`. Establish `h2` using `div_mem_adjoin (F := F) u v hv'`. Establish `key : w j / v' = (w j / v) / (v' / v)`.

Clear the denominators using the available nonvanishing facts. Use `show w j / v' ∈ IntermediateField.adjoin F (Set.range fun i => u i / v)`. Rewrite using `[key]`. Conclude with `div_mem h1 h2`.
-/
theorem adjoin_le {I J : Type} (u : I → M) (w : J → M) (v v' : M)
    (hw : ∀ j, w j ∈ Submodule.span F (Set.range u)) (hv' : v' ∈ Submodule.span F (Set.range u))
    (hv : v ≠ 0) (hv'0 : v' ≠ 0) :
    IntermediateField.adjoin F (Set.range fun j => w j / v') ≤
      IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  have h1 := div_mem_adjoin (F := F) u v (hw j)
  have h2 := div_mem_adjoin (F := F) u v hv'
  have key : w j / v' = (w j / v) / (v' / v) := by
    field_simp
  show w j / v' ∈ IntermediateField.adjoin F (Set.range fun i => u i / v)
  rw [key]
  exact div_mem h1 h2

/- English proof (translation)
Introduce `F M _ _ _ I J u w v v' hspan hv hv' hv0 hv'0`. Apply `le_antisymm` to reduce the goal to its premises. Apply `adjoin_le w u v' v` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← hspan]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Rewrite using `[← hspan]`. Conclude with `hv`. Conclude with `hv'0`. Conclude with `hv0`.

Apply `adjoin_le u w v v'` to reduce the goal to its premises. Introduce `j`. Rewrite using `[hspan]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Conclude with `hv'`.

Conclude with `hv0`. Conclude with `hv'0`.
-/
theorem full : RatioFieldSpan.Statement := by
  intro F M _ _ _ I J u w v v' hspan hv hv' hv0 hv'0
  apply le_antisymm
  · apply adjoin_le w u v' v
    · intro i
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [← hspan]; exact hv
    · exact hv'0
    · exact hv0
  · apply adjoin_le u w v v'
    · intro j
      rw [hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    · exact hv'
    · exact hv0
    · exact hv'0

end RatioFieldSpan

end GroundTheory.Heights₂.Heights.LowerBoundFree
