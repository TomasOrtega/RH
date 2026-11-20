import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

/- English proof (translation)
Introduce `K _ _ n a d ha hd _ μ hμ m k b c hbc hmk`. Take `⟨τ, -, hτ⟩` from `hQ K n a d ha hd m k b c hbc hmk`. Establish `hf : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Establish `key : ∀ j, (Module.finrank ℚ K : ℝ) * μ ≤ Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j))`. Introduce `j`.

Establish `h` using `hμ (τ j)`. Rewrite `h` using `[hL K n a d (τ j), normalise, le_div_iff₀ hf]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : ∑ _j : Fin k, (Module.finrank ℚ K : ℝ) * μ ≤ ∑ j, (Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j)))` using `Finset.sum_le_sum fun j _ => key j`. Rewrite `hsum` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Rewrite using `[normalise, le_div_iff₀ hf]`. Establish `e : (k : ℝ) * μ * (Module.finrank ℚ K : ℝ) = (k : ℝ) * ((Module.finrank ℚ K : ℝ) * μ)`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem OrthogonalLines.proof (hQ : LinesQuotDegreeBound.Statement)
    (hL : LinesLineDegree.Statement) : OrthogonalLines.Statement := by
  intro K _ _ n a d ha hd _ μ hμ m k b c hbc hmk
  obtain ⟨τ, -, hτ⟩ := hQ K n a d ha hd m k b c hbc hmk
  have hf : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have key : ∀ j, (Module.finrank ℚ K : ℝ) * μ ≤
      Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j)) := by
    intro j
    have h := hμ (τ j)
    rw [hL K n a d (τ j), normalise, le_div_iff₀ hf] at h
    linarith
  have hsum : ∑ _j : Fin k, (Module.finrank ℚ K : ℝ) * μ ≤
      ∑ j, (Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j))) :=
    Finset.sum_le_sum fun j _ => key j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [normalise, le_div_iff₀ hf]
  have e : (k : ℝ) * μ * (Module.finrank ℚ K : ℝ) = (k : ℝ) * ((Module.finrank ℚ K : ℝ) * μ) := by
    ring
  linarith

end GroundTheory.Heights₂.Heights
