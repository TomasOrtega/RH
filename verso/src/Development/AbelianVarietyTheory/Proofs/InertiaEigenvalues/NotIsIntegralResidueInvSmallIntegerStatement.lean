import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsIntegralResidueInvSmallInteger
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NotIntegral.inv_small_not_integral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNotIsIntegralResidueInvSmallInteger.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.not_isIntegral_residue_inv_small_integer : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  first | exact @GlobalTheory.NotIntegral.inv_small_not_integral | exact GlobalTheory.NotIntegral.inv_small_not_integral | (intros; apply GlobalTheory.NotIntegral.inv_small_not_integral <;> assumption)
