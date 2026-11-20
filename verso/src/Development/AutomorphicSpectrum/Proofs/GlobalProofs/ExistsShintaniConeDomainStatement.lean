import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomain
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FExistsShintaniConeDomain.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.exists_shintani_cone_domain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain <;> assumption)
