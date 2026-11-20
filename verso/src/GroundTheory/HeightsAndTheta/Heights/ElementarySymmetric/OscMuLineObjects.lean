import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample.OscWeight
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

namespace OscLine

def oscRho (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  Real.exp (2 * Taut.oscW (z ⟨(), 1⟩ / z ⟨(), 0⟩))

def oscMuNorm (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  Real.sqrt (oscRho z) / Real.sqrt (‖z ⟨(), 0⟩‖ ^ 2 + oscRho z * ‖z ⟨(), 1⟩‖ ^ 2)

def oscMuLine : HermLine (PBlk 2) := hermOfFun (PBlk 2) (fun _ => -1) oscMuNorm

/- English proof (translation)
The claim follows from `Real.exp_pos _`.
-/
theorem oscRho_pos (z : (Σ _ : Unit, Fin 2) → ℂ) : 0 < oscRho z := Real.exp_pos _

/- English proof (translation)
Unfold `oscRho torusSmul`. Use `congr 3`. Conclude with `mul_div_mul_left _ _ (hc ())`.
-/
theorem oscRho_smul (c : Unit → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ _ : Unit, Fin 2) → ℂ) :
    oscRho (torusSmul c z) = oscRho z := by
  unfold oscRho torusSmul
  congr 3
  exact mul_div_mul_left _ _ (hc ())

/- English proof (translation)
Take `⟨i, hi⟩` from `hz`. Establish `hρ` using `oscRho_pos z`. Establish `hs : 0 < ‖z ⟨(), 0⟩‖ ^ 2 + oscRho z * ‖z ⟨(), 1⟩‖ ^ 2` using `by fin_cases i`. Establish `: 0 < ‖z ⟨(), 0⟩‖ ^ 2` using `by positivity`. Check the signs of the components of the expression.

Establish `: 0 < ‖z ⟨(), 1⟩‖ ^ 2` using `by positivity`. Check the signs of the components of the expression. Conclude with `div_pos (Real.sqrt_pos.mpr hρ) (Real.sqrt_pos.mpr hs)`.
-/
theorem oscMuNorm_pos {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0) : 0 < oscMuNorm z := by
  obtain ⟨i, hi⟩ := hz
  have hρ := oscRho_pos z
  have hs : 0 < ‖z ⟨(), 0⟩‖ ^ 2 + oscRho z * ‖z ⟨(), 1⟩‖ ^ 2 := by
    fin_cases i
    · have : 0 < ‖z ⟨(), 0⟩‖ ^ 2 := by positivity
      positivity
    · have : 0 < ‖z ⟨(), 1⟩‖ ^ 2 := by positivity
      positivity
  exact div_pos (Real.sqrt_pos.mpr hρ) (Real.sqrt_pos.mpr hs)

/- English proof (translation)
Introduce `c z hc`. Establish `hρ` using `oscRho_smul c hc z`. Establish `hc0 : 0 < ‖c ()‖` using `norm_pos_iff.mpr (hc ())`. Simplify using `only [oscMuNorm, hρ, Finset.univ_unique, Finset.prod_singleton, zpow_neg, zpow_one]`. Simplify using `only [torusSmul, norm_mul]`.

Establish `: (‖c ()‖ * ‖z ⟨(), 0⟩‖) ^ 2 + oscRho z * (‖c ()‖ * ‖z ⟨(), 1⟩‖) ^ 2 = ‖c ()‖ ^ 2 * (‖z ⟨(), 0⟩‖ ^ 2 + oscRho z * ‖z ⟨(), 1⟩‖ ^ 2)` using `by ring`. Rewrite using `[this, Real.sqrt_mul (by positivity), Real.sqrt_sq hc0.le]`. Clear the denominators using the available nonvanishing facts.
-/
theorem oscMuNorm_homog : IsHomogOfDeg (ι := PBlk 2) (fun _ => -1) oscMuNorm := by
  intro c z hc
  have hρ := oscRho_smul c hc z
  have hc0 : 0 < ‖c ()‖ := norm_pos_iff.mpr (hc ())
  simp only [oscMuNorm, hρ, Finset.univ_unique, Finset.prod_singleton, zpow_neg, zpow_one]
  simp only [torusSmul, norm_mul]
  have : (‖c ()‖ * ‖z ⟨(), 0⟩‖) ^ 2 + oscRho z * (‖c ()‖ * ‖z ⟨(), 1⟩‖) ^ 2 =
      ‖c ()‖ ^ 2 * (‖z ⟨(), 0⟩‖ ^ 2 + oscRho z * ‖z ⟨(), 1⟩‖ ^ 2) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hc0.le]
  field_simp

end OscLine

end GroundTheory.Heights₂.Heights.LowerBoundFree
