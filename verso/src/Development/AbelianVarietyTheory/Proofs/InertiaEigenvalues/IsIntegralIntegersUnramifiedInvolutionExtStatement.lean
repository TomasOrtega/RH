import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIntegersUnramifiedInvolutionExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.Unr.intO` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsIntegralIntegersUnramifiedInvolutionExt.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by
  first | exact @GlobalTheory.UnitLemma.Unr.intO | exact GlobalTheory.UnitLemma.Unr.intO | (intros; apply GlobalTheory.UnitLemma.Unr.intO <;> assumption)
