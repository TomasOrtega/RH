import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConePolar
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaneSliceMass
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coneIntegral_space_one (e : ℕ) :
    coneIntegral (HermNorm.std (e + 1)) (⊥ : Ideal (MvPolynomial (Fin (e + 1)) ℂ)) e
      (fun _ => 1) = 1 := by
  have hS : {y : EuclideanSpace ℂ (Fin (e + 1)) | ‖y‖ < 1 ∧
        ∀ q ∈ (⊥ : Ideal (MvPolynomial (Fin (e + 1)) ℂ)),
          eval ((HermNorm.std (e + 1)).pointOf y) q = 0} =
      {y : EuclideanSpace ℂ (Fin (e + 1)) | ‖y‖ < 1 ∧ ∀ j : Fin (e + 1), e + 1 ≤ (j : ℕ) → y j = 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Ideal.mem_bot]
    refine and_congr_right fun _ => ⟨fun _ j hj => absurd j.isLt (by omega), fun _ q hq => ?_⟩
    rw [hq, map_zero]
  obtain ⟨h0, htop⟩ := coordBall_mass (n := e + 1) (m := e + 1) le_rfl
  rw [coneIntegral, hS, setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  exact div_self (ENNReal.toReal_ne_zero.mpr ⟨h0.ne', htop.ne⟩)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem ConeToProjective.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConePolar.Statement)
    (h₃ : PlaneSliceMass.Statement) : ConeToProjective.Statement := by
  intro n e h J F ℓ g hJ hF hℓ hg hgc
  obtain ⟨κ, hκ⟩ := h₂ e
  have hplane := hκ (e + 1) (HermNorm.std (e + 1)) ⊥ (Pi.single 0 1) (fun _ => 1)
    (isProjPrime_bot_space e) (space_dim (e + 1)) (linForm_single_not_mem_bot 0)
    (fun _ _ _ => rfl) continuousOn_const
  rw [coneIntegral_space_one, linForm_single, bot_sup_eq, h₃ e, mul_one] at hplane
  rw [hκ n h J ℓ g hJ (h₁ ℂ n (e + 1) J F hJ hF) hℓ hg hgc, ← hplane, one_mul]

end

end GroundTheory.Heights₂.Heights
