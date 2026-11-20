import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem homotheticLattice : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair,
    (∀ z, z ∈ L'.lattice ↔ c * z ∈ L.lattice) ∧ L'.g₂ = c ^ 4 * L.g₂ ∧ L'.g₃ = c ^ 6 * L.g₃ ∧
    (∀ z, L'.weierstrassP z = c ^ 2 * L.weierstrassP (c * z) ∧
      L'.derivWeierstrassP z = c ^ 3 * L.derivWeierstrassP (c * z)) ∧
    ∀ d, HasCMBy d L → HasCMBy d L' := by
  intro L c hc
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  obtain ⟨hmem, -, -, hwp, -, -, -, -, -, hg2, hg3⟩ := Formalism.L2.Th1.F.homogeneity L c⁻¹ hc'
  refine ⟨Formalism.L2.Th1.F.scalePair L c⁻¹ hc', ?_, ?_, ?_, ?_, ?_⟩
  · intro z; rw [hmem, inv_inv]
  · rw [hg2, inv_pow, inv_inv]
  · rw [hg3, inv_pow, inv_inv]
  · intro z
    constructor
    · have := hwp (c * z)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul, inv_pow, inv_inv] at this
      exact this
    · unfold PeriodPair.derivWeierstrassP
      rw [Formalism.L2.Th1.F.Homog.tsum_scale L c⁻¹ hc' (fun l => 2 / (z - l) ^ 3), mul_neg,
        ← tsum_mul_left]
      congr 1
      refine tsum_congr fun l => ?_
      have : z - c⁻¹ * (l : ℂ) = c⁻¹ * (c * z - l) := by field_simp
      rw [this, mul_pow, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
  · intro d hd
    exact Formalism.L2.Th1.F.hasCMByScale d L c⁻¹ hc' hd

end GlobalTheory
