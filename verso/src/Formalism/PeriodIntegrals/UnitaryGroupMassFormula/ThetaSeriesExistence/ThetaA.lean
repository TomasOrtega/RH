import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaDerivNe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.Development

noncomputable section

open Complex

namespace PI.SSE

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
lemma th_add_one (τ u : ℂ) : th τ (u + 1) = -th τ u := by
  unfold th
  rw [show u + 1 + (1 / 2 + τ / 2) = (u + (1 / 2 + τ / 2)) + 1 by ring, jacobiTheta₂_add_left]
  have key : cexp (↑Real.pi * I * (u + 1)) = -cexp (↑Real.pi * I * u) := by
    rw [show ↑Real.pi * I * (u + 1) = ↑Real.pi * I * u + ↑Real.pi * I by ring, Complex.exp_add,
      Complex.exp_pi_mul_I]
    ring
  rw [key]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
lemma th_add_tau (τ u : ℂ) :
    th τ (u + τ) = -(cexp (-(Real.pi * I * τ) - 2 * Real.pi * I * u) * th τ u) := by
  unfold th
  rw [show u + τ + (1 / 2 + τ / 2) = (u + (1 / 2 + τ / 2)) + τ by ring, jacobiTheta₂_add_left']
  have key : cexp (↑Real.pi * I * (u + τ)) * cexp (-↑Real.pi * I * (τ + 2 * (u + (1 / 2 + τ / 2)))) =
      -(cexp (-(↑Real.pi * I * τ) - 2 * ↑Real.pi * I * u) * cexp (↑Real.pi * I * u)) := by
    calc cexp (↑Real.pi * I * (u + τ)) * cexp (-↑Real.pi * I * (τ + 2 * (u + (1 / 2 + τ / 2))))
        = cexp ((-(↑Real.pi * I * τ) - 2 * ↑Real.pi * I * u + ↑Real.pi * I * u) - ↑Real.pi * I) := by
          rw [← Complex.exp_add]
          congr 1
          ring
      _ = -(cexp (-(↑Real.pi * I * τ) - 2 * ↑Real.pi * I * u) * cexp (↑Real.pi * I * u)) := by
          rw [Complex.exp_sub, Complex.exp_pi_mul_I, Complex.exp_add]
          ring
  rw [← mul_assoc, key]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
lemma th_neg (τ u : ℂ) : th τ (-u) = -th τ u := by
  unfold th
  have h1 : jacobiTheta₂ (u + (1 / 2 + τ / 2)) τ =
      cexp (-↑Real.pi * I * (τ + 2 * (u - (1 / 2 + τ / 2)))) * jacobiTheta₂ (u - (1 / 2 + τ / 2)) τ := by
    rw [show u + (1 / 2 + τ / 2) = (u - (1 / 2 + τ / 2) + τ) + 1 by ring, jacobiTheta₂_add_left,
      jacobiTheta₂_add_left']
  rw [show -u + (1 / 2 + τ / 2) = -(u - (1 / 2 + τ / 2)) by ring, jacobiTheta₂_neg_left, h1]
  have key : cexp (↑Real.pi * I * u) * cexp (-↑Real.pi * I * (τ + 2 * (u - (1 / 2 + τ / 2)))) =
      -cexp (↑Real.pi * I * -u) := by
    calc cexp (↑Real.pi * I * u) * cexp (-↑Real.pi * I * (τ + 2 * (u - (1 / 2 + τ / 2))))
        = cexp (↑Real.pi * I * -u + ↑Real.pi * I) := by
          rw [← Complex.exp_add]
          congr 1
          ring
      _ = -cexp (↑Real.pi * I * -u) := by
          rw [Complex.exp_add, Complex.exp_pi_mul_I]
          ring
  rw [← mul_assoc, key]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
lemma th_diff (τ : ℂ) (hτ : 0 < τ.im) : Differentiable ℂ (th τ) := by
  intro u
  unfold th
  exact (((differentiableAt_id.const_mul (↑Real.pi * I)).cexp)).mul
    ((differentiableAt_jacobiTheta₂_fst (u + (1 / 2 + τ / 2)) hτ).comp u (differentiableAt_id.add_const _))

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
lemma th_zero (τ : ℂ) : th τ 0 = 0 := by
  have h := th_neg τ 0
  rw [neg_zero] at h
  linear_combination h / 2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma th_deriv (τ : ℂ) (hτ : 0 < τ.im) : deriv (th τ) 0 = jacobiTheta₂' (1 / 2 + τ / 2) τ := by
  have h2 : HasDerivAt (fun u ↦ jacobiTheta₂ (u + (1 / 2 + τ / 2)) τ) (jacobiTheta₂' (0 + (1 / 2 + τ / 2)) τ) 0 :=
    (hasDerivAt_jacobiTheta₂_fst (0 + (1 / 2 + τ / 2)) hτ).comp_add_const 0 _
  have h1 : HasDerivAt (fun u : ℂ ↦ cexp (↑Real.pi * I * u)) (cexp (↑Real.pi * I * 0) * (↑Real.pi * I * 1)) 0 :=
    ((hasDerivAt_id' 0).const_mul (↑Real.pi * I)).cexp
  have hd : HasDerivAt (th τ) _ 0 := h1.mul h2
  rw [hd.deriv]
  have hz : jacobiTheta₂ (0 + (1 / 2 + τ / 2)) τ = 0 := by
    have h0 := th_zero τ
    simpa [th] using h0
  rw [hz]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem thetaA : ThetaA := by
  intro τ hτ
  exact ⟨th_diff τ hτ, th_neg τ, th_add_one τ, th_add_tau τ, th_deriv τ hτ⟩

end PI.SSE

end
