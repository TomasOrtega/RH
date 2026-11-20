import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul

noncomputable section

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem stProfile_holds : StProfile := by
  intro N
  induction N with
  | zero =>
    refine ⟨fun x => expNegInvGlue (1 - x), ?_, ?_, ?_, ?_⟩
    · exact expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
    · intro x hx
      exact expNegInvGlue.zero_of_nonpos (by linarith)
    · intro x
      simpa using expNegInvGlue.nonneg _
    · simpa using expNegInvGlue.pos_of_pos (x := 1) one_pos
  | succ N ih =>
    obtain ⟨G, h1, h2, h3, h4⟩ := ih
    have hc : Continuous G := h1.continuous
    have hd : deriv (fun x => ∫ s in (1:ℝ)..x, G s) = G := by
      funext x
      exact (hc.deriv_integral G 1 x)
    refine ⟨fun x => ∫ s in (1:ℝ)..x, G s, ?_, ?_, ?_, ?_⟩
    · rw [contDiff_infty_iff_deriv, hd]
      exact ⟨fun x => (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).differentiableAt, h1⟩
    · intro x hx
      have : ∫ s in (1:ℝ)..x, G s = ∫ s in (1:ℝ)..x, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hx] at hs
        exact h2 s hs.1
      simpa using this
    · intro x
      rw [iteratedDeriv_succ', hd]
      exact h3 x
    · rw [iteratedDeriv_succ', hd]
      exact h4

/- English proof (translation)
A detailed English derivation is pending.
-/
example : GlobalTheory.PsCo.Pc1.StProfile := stProfile_holds

end GlobalTheory.PsCo.Pc1
