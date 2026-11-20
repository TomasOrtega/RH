import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassParametrizationExists
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRayClassParametrizationExists.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.ray_class_parametrization_exists : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 → ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top <;> assumption)
