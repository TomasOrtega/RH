import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

/- English proof (translation)
Rewrite using `[hd, hd]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Use `absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))` and prove the remaining obligations. Rewrite `hk`, the goal using `[Finset.mem_filter]`. Conclude with `⟨hk.1, lt_of_not_ge fun h' => absurd hk.2 (not_lt.2 (hne k hk.1 h'))⟩`. Introduce and unpack `⟨k, hk, h1, h2⟩`. Use `Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩` and prove the remaining obligations.

Rewrite `hx`, the goal using `[Finset.mem_filter]`. Conclude with `⟨hx.1, lt_of_lt_of_le hx.2 (h1.trans h2.le)⟩`. Use `h (Finset.mem_filter.2 ⟨hk, h2⟩)` as an intermediate fact. Conclude with `absurd (Finset.mem_filter.1 this).2 (not_lt.2 h1)`.
-/
theorem depth_lt_iff {r : ℕ} (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r) (d : Fin s → ℕ)
    (hd : ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) (i j : Fin s) :
    d j < d i ↔ ∃ k ∈ S, Fin.castLE hs j ≤ k ∧ k < Fin.castLE hs i := by
  rw [hd, hd]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_not_ge fun h' => absurd hk.2 (not_lt.2 (hne k hk.1 h'))⟩
  · rintro ⟨k, hk, h1, h2⟩
    refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
    · rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_of_lt_of_le hx.2 (h1.trans h2.le)⟩
    · have := h (Finset.mem_filter.2 ⟨hk, h2⟩)
      exact absurd (Finset.mem_filter.1 this).2 (not_lt.2 h1)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.mul_apply]`.
-/
theorem cT_submatrix_mul {E : Type} [Field E] (σ : E →+* E) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (A B : Matrix (Fin n) (Fin r) E) (f g : Fin s → Fin r) :
    Formalism.UG.cT σ (A.submatrix id f) * J * B.submatrix id g = (Formalism.UG.cT σ A * J * B).submatrix f g := by
  ext i j
  simp [Formalism.UG.cT, Matrix.mul_apply]

end GlobalTheory.TieStd
