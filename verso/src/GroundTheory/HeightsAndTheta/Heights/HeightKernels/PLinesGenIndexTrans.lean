import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexTrans

/- English proof (translation)
The claim follows from `Submodule.span_int_eq_addSubgroupClosure s`.
-/
theorem toAddSubgroup_span {V : Type} [AddCommGroup V] (s : Set V) :
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
  Submodule.span_int_eq_addSubgroupClosure s

end KLinesGenIndexTrans

open KLinesGenIndexTrans in

/- English proof (translation)
Introduce `V _ _ _ A B C hA hB hC`. Take `⟨bA, rfl⟩` from `h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) A hA`. Take `⟨bB, rfl⟩` from `h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) B hB`. Take `⟨bC, rfl⟩` from `h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) C hC`. Establish `hAB` using `h2 V _ bA bB _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)`.

Establish `hBC` using `h2 V _ bB bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)`. Establish `hAC` using `h2 V _ bA bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hAB]`. Establish `h0 : (bA.det bB : ℚ) ≠ 0` using `(bA.isUnit_det bB).ne_zero`.

Check the signs of the components of the expression. Rewrite using `[hAB, hBC, hAC, ← abs_mul, ← Rat.cast_mul, Module.Basis.det_mul_det]`.
-/
theorem LinesGenIndexTrans.proof (h1 : LinesLatticeBasis.Statement)
    (h2 : LinesGenIndexDet.Statement) : LinesGenIndexTrans.Statement := by
  intro V _ _ _ A B C hA hB hC
  classical
  obtain ⟨bA, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) A hA
  obtain ⟨bB, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) B hB
  obtain ⟨bC, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) C hC
  have hAB := h2 V _ bA bB _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hBC := h2 V _ bB bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hAC := h2 V _ bA bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  refine ⟨?_, ?_⟩
  · rw [hAB]
    have h0 : (bA.det bB : ℚ) ≠ 0 := (bA.isUnit_det bB).ne_zero
    positivity
  · rw [hAB, hBC, hAC, ← abs_mul, ← Rat.cast_mul, Module.Basis.det_mul_det]

end GroundTheory.Heights₂.Heights
