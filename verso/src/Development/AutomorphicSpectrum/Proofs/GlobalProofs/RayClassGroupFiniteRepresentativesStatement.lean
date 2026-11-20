import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassGroupFiniteRepresentatives
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FRayClassGroupFiniteRepresentatives.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.ray_class_group_finite_representatives : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ S : Finset (Ideal (𝓞 F)), (∀ a ∈ S, CoprimeTo F 𝔣 a) ∧ (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) ∧
    ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay <;> assumption)
