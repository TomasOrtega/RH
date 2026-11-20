import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormModEqOfRayRelPowMod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RayFacts.absNorm_modEq_of_rayRel_powMod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAbsNormModEqOfRayRelPowMod.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.absNorm_modEq_pow_of_rayRel_powMod : ∀ (F : Type) [Field F] [NumberField F] (l m : ℕ) (I J : Ideal (𝓞 F)), RayRel F (powMod F l m) I J → Ideal.absNorm I ≡ Ideal.absNorm J [MOD l ^ m] := by
  first | exact @GlobalTheory.CompanionTheory.RayFacts.absNorm_modEq_of_rayRel_powMod | exact GlobalTheory.CompanionTheory.RayFacts.absNorm_modEq_of_rayRel_powMod | (intros; apply GlobalTheory.CompanionTheory.RayFacts.absNorm_modEq_of_rayRel_powMod <;> assumption)
