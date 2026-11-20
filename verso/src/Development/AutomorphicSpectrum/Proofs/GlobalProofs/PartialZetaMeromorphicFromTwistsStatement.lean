import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaMeromorphicFromTwists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FPartialZetaMeromorphicFromTwists.lean&line=166#L166)
-/
theorem _root_.GlobalTheory.T.partial_zeta_meromorphic_from_twists : ∀ (G : Type) [Fintype G] (D T T' : G → ℂ → ℂ) (l l' : ℕ) (τ τ' : Equiv.Perm G), l.Prime → l'.Prime → l ≠ l' →
  (∀ c, Differentiable ℂ (T c)) → (∀ c, Differentiable ℂ (T' c)) →
  (∀ c s, 1 < s.re → (l : ℂ) ^ (1 - s) * D (τ c) s - D c s = T c s) →
  (∀ c s, 1 < s.re → (l' : ℂ) ^ (1 - s) * D (τ' c) s - D c s = T' c s) →
  ∃ Z : G → ℂ → ℂ, (∀ c, DifferentiableOn ℂ (Z c) {1}ᶜ) ∧ (∀ c s, 1 < s.re → Z c s = D c s) ∧
    ∀ k : ℕ, 1 ≤ k → (∀ c, ∃ q : ℚ, T c (1 - (k : ℂ)) = (q : ℂ)) → ∀ c, ∃ q : ℚ, Z c (1 - (k : ℂ)) = (q : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations.continuation_of_two_relations | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations.continuation_of_two_relations | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations.continuation_of_two_relations <;> assumption)
