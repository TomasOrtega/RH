import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PSpecB

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem toMK_inv_eq_conjTranspose {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h : toMK k⁻¹ = star (toMK k) :=
    Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem (show toMK k ∈ Kset ε from k.2).1)
  rw [h, Matrix.star_eq_conjTranspose]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem conj_pmat_eq_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    toMK k⁻¹ * pmat z * toMK k = pmat (adK k⁻¹ z) := by
  rw [pmat_adK, toMK_inv_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem pmat_real_smul {ε : Fin n → Bool} (t : ℝ) (z : PCoord ε → ℂ) :
    pmat ((t : ℂ) • z) = (t : ℂ) • pmat z := by
  rw [Complex.coe_smul, adKAux_pmat_smul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the hypotheses and the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhoP_real_smul {ε : Fin n → Bool} (t : ℝ) (z : PCoord ε → ℂ) : rhoP ((t : ℂ) • z) = |t| * rhoP z := by
  have hS : ∑ ab, ‖((t : ℂ) • z) ab‖ ^ 2 = t ^ 2 * ∑ ab, ‖z ab‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    simp [Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold rhoP
  rw [hs_pmat, hs_pmat, hS, show 2 * (t ^ 2 * ∑ ab, ‖z ab‖ ^ 2) = t ^ 2 * (2 * ∑ ab, ‖z ab‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  ring

end ReciprocityTheory.ChartRestriction.DS
