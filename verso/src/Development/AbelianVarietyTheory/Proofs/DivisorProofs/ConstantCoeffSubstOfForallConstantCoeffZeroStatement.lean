import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.constantCoeff_subst_of_constantCoeff_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConstantCoeffSubstOfForallConstantCoeffZero.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero : ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R), (∀ i, constantCoeff (a i) = 0) → ∀ g : MvPowerSeries σ R, constantCoeff (subst a g) = constantCoeff g := by
  first | exact @GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | exact GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | (intros; apply GlobalTheory.constantCoeff_subst_of_constantCoeff_zero <;> assumption)
