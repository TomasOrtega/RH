import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralResidueComapInvolutionIff
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsIntegralResidueComapInvolutionIff.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.isIntegral_residue_comap_involution_iff : ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A), IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔ IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff | exact GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff | (intros; apply GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff <;> assumption)
