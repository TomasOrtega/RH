import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FRayClassConeParametrization.lean&line=345#L345)
-/
theorem _root_.GlobalTheory.T.ray_class_cone_parametrization : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam <;> assumption)
