import Mathlib
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo

/- English proof (translation)
Introduce `T Ω _ _ u f S hS F hF hf s`. Take `⟨s, hs⟩` from `s`. Substitute `hS` using the available equality. Use `show ∃ (G : MvPolynomial T ℚ) (k : ℕ), s * f ^ k = aeval u G`. Proceed by induction on `hs using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Break down `hx with rfl | ⟨i, rfl⟩` into its components or cases. Conclude with `⟨1, 1, by simp [hf]⟩`. Conclude with `⟨X i, 0, by simp⟩`. Consider the case `algebraMap q => exact ⟨C q, 0, by simp⟩`.

Consider the case `add x y _ _ ihx ihy`. Take `⟨G₁, k₁, h₁⟩` from `ihx`. Take `⟨G₂, k₂, h₂⟩` from `ihy`. Use `⟨G₁ * F ^ k₂ + G₂ * F ^ k₁, k₁ + k₂, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_pow, hF, ← h₁, ← h₂]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y _ _ ihx ihy`. Take `⟨G₁, k₁, h₁⟩` from `ihx`. Take `⟨G₂, k₂, h₂⟩` from `ihy`. Use `⟨G₁ * G₂, k₁ + k₂, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_mul, ← h₁, ← h₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_numerator_of_mem_adjoin_insert_inv :
    ∀ (T : Type) (Ω : Type) [Field Ω] [CharZero Ω] (u : T → Ω) (f : Ω) (S : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert f⁻¹ (Set.range u)) → ∀ F : MvPolynomial T ℚ, aeval u F = f → f ≠ 0 → ∀ s : S,
    ∃ (G : MvPolynomial T ℚ) (k : ℕ), (s : Ω) * f ^ k = aeval u G := by
  intro T Ω _ _ u f S hS F hF hf s
  obtain ⟨s, hs⟩ := s
  subst hS
  show ∃ (G : MvPolynomial T ℚ) (k : ℕ), s * f ^ k = aeval u G
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨i, rfl⟩
    · exact ⟨1, 1, by simp [hf]⟩
    · exact ⟨X i, 0, by simp⟩
  | algebraMap q => exact ⟨C q, 0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨G₁, k₁, h₁⟩ := ihx
    obtain ⟨G₂, k₂, h₂⟩ := ihy
    refine ⟨G₁ * F ^ k₂ + G₂ * F ^ k₁, k₁ + k₂, ?_⟩
    simp only [map_add, map_mul, map_pow, hF, ← h₁, ← h₂]
    ring
  | mul x y _ _ ihx ihy =>
    obtain ⟨G₁, k₁, h₁⟩ := ihx
    obtain ⟨G₂, k₂, h₂⟩ := ihy
    refine ⟨G₁ * G₂, k₁ + k₂, ?_⟩
    simp only [map_mul, ← h₁, ← h₂]
    ring

end GlobalTheory.CompanionTheory.Ggeo
