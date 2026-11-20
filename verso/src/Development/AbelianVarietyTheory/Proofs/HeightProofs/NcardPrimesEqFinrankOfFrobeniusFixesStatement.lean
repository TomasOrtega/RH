import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardPrimesEqFinrankOfFrobeniusFixes
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FNcardPrimesEqFinrankOfFrobeniusFixes.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.ncard_primes_eq_finrank_of_frobenius_fixes : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x) → {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard = Module.finrank K M := by
  first | exact @GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix | exact GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix | (intros; apply GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix <;> assumption)
