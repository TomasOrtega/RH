import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem unitMinorSet_rank_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → Y.rank = n := by
  intro k _ _ _ _ n d Y hY
  obtain ⟨-, f, hf⟩ := hY
  have hdet : (Y.submatrix id f).det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hf
    exact zero_ne_one hf
  have hunit : IsUnit (Y.submatrix id f) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsub : (Y.submatrix id f).rank = n := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  have hmul : Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f = Y.submatrix id f := by
    rw [Matrix.mul_submatrix_one]; rfl
  apply le_antisymm (Matrix.rank_le_height Y)
  calc n = (Y.submatrix id f).rank := hsub.symm
    _ = (Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f).rank := by rw [hmul]
    _ ≤ Y.rank := Matrix.rank_mul_le_left _ _

end GlobalTheory
