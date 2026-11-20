import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp

/- English proof (translation)
Introduce `Ω _ _ σ τ F S hf hS s`. Take `⟨x, hx⟩` from `s`. Substitute `hS` using the available equality. Express the relevant statement in the definitionally equal form `∃ (N : ℕ) (G : MvPolynomial σ ℚ), x * aeval τ F ^ N = aeval τ G`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Break down `hy with rfl | ⟨q, rfl⟩` into its components or cases. Conclude with `⟨1, 1, by simp [hf]⟩`. Conclude with `⟨0, X q, by simp⟩`. Consider the case `algebraMap r`.

Conclude with `⟨0, C r, by simp [MvPolynomial.algebraMap_eq]⟩`. Consider the case `add a b _ _ iha ihb`. Take `⟨N, G, h⟩` from `iha`. Take `⟨M, H, h'⟩` from `ihb`. Use `⟨N + M, G * F ^ M + H * F ^ N, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_pow, ← h, ← h']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul a b _ _ iha ihb`. Take `⟨N, G, h⟩` from `iha`. Take `⟨M, H, h'⟩` from `ihb`.

Use `⟨N + M, G * H, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, ← h, ← h']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_pow_eq_aeval_of_mem_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω), aeval τ F ≠ 0 →
      S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      ∀ s : S, ∃ (N : ℕ) (G : MvPolynomial σ ℚ), (s : Ω) * aeval τ F ^ N = aeval τ G := by
  intro Ω _ _ σ τ F S hf hS s
  obtain ⟨x, hx⟩ := s
  subst hS
  change ∃ (N : ℕ) (G : MvPolynomial σ ℚ), x * aeval τ F ^ N = aeval τ G
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨q, rfl⟩
    · exact ⟨1, 1, by simp [hf]⟩
    · exact ⟨0, X q, by simp⟩
  | algebraMap r =>
    exact ⟨0, C r, by simp [MvPolynomial.algebraMap_eq]⟩
  | add a b _ _ iha ihb =>
    obtain ⟨N, G, h⟩ := iha
    obtain ⟨M, H, h'⟩ := ihb
    refine ⟨N + M, G * F ^ M + H * F ^ N, ?_⟩
    simp only [map_add, map_mul, map_pow, ← h, ← h']
    ring
  | mul a b _ _ iha ihb =>
    obtain ⟨N, G, h⟩ := iha
    obtain ⟨M, H, h'⟩ := ihb
    refine ⟨N + M, G * H, ?_⟩
    simp only [map_mul, ← h, ← h']
    ring

end GlobalTheory.CompanionTheory.Ar.Cmp
