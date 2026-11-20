import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

/- English proof (translation)
Use `⟨72 * Real.exp 4, by positivity, ?_⟩` and prove the remaining obligations. Introduce `g Y ρ hY hρ hmin u`. Take `⟨hsum, Λ, hΛ, hle⟩` from `hPD g Y ρ hY hρ hmin u`. Use `⟨hsum, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos g with rfl | hg` into its components or cases.

Establish `hq : ∀ k : Fin 0 → ℤ, qf Y (intVec k + u) = 0` using `fun k => by simp [qf]`. Simplify using `only [hq, mul_zero, Real.exp_zero, tsum_const, Nat.card_unique, one_smul, Nat.cast_zero, zero_div, Real.rpow_zero, Matrix.det_isEmpty, Real.one_rpow, pow_zero, mul_one, le_refl]`. Establish `hdet : 0 < Y.det` using `hY.det_pos`. Establish `hd : 0 ≤ Y.det ^ (-(1 / 2 : ℝ))` using `Real.rpow_nonneg hdet.le _`. Establish `hS` using `(hSS g hg Λ ρ hρ hΛ).2`.

Establish `hc` using `hC g hg`. Establish `hr : 0 ≤ (1 + 1 / ρ) ^ g` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GaussianSum.proof (hPD : GaussPoissonDual.Statement) (hSS : GaussShellSum.Statement)
    (hC : GaussConstant.Statement) : GaussianSum.Statement := by
  refine ⟨72 * Real.exp 4, by positivity, ?_⟩
  intro g Y ρ hY hρ hmin u
  obtain ⟨hsum, Λ, hΛ, hle⟩ := hPD g Y ρ hY hρ hmin u
  refine ⟨hsum, ?_⟩
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hq : ∀ k : Fin 0 → ℤ, qf Y (intVec k + u) = 0 := fun k => by simp [qf]
    simp only [hq, mul_zero, Real.exp_zero, tsum_const, Nat.card_unique, one_smul,
      Nat.cast_zero, zero_div, Real.rpow_zero, Matrix.det_isEmpty, Real.one_rpow, pow_zero,
      mul_one, le_refl]
  · have hdet : 0 < Y.det := hY.det_pos
    have hd : 0 ≤ Y.det ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hdet.le _
    have hS := (hSS g hg Λ ρ hρ hΛ).2
    have hc := hC g hg
    have hr : 0 ≤ (1 + 1 / ρ) ^ g := by positivity
    calc ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u))
        ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := hle
      _ ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) * (2 * gaussShellConst g * (1 + 1 / ρ) ^ g) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = √2 ^ g * (2 * gaussShellConst g) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g := by ring
      _ ≤ (72 * Real.exp 4 * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hd) hr

end GroundTheory.Heights₂.Heights
