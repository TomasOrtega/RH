import Mathlib

namespace GlobalTheory.SublatticeFacts

open Matrix

/- English proof (translation)
Take `⟨t, rfl⟩` from `hfg`. Use `choose f hf1 hf using fun v : n → A => hden (X *ᵥ v)`. Use `⟨∏ v ∈ t, f v, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ => by have := hf1 v; omega)`. Introduce `y hy`.

Rewrite using `[Nat.cast_smul_eq_nsmul A]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Rewrite using `[← Finset.mul_prod_erase t f hx, mul_nsmul, ← Nat.cast_smul_eq_nsmul A (f x)]`. Conclude with `Submodule.smul_of_tower_mem _ (∏ v ∈ t.erase x, f v) (hf x)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[Matrix.mulVec_add, smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Establish `: X *ᵥ (a • x) = a • (X *ᵥ x)`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]`. Rewrite using `[this, smul_comm]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem finiteRing_sq_sub_mul_sq_eq_of_card {A : Type} [CommRing A] {S : Subring A} {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)) (hfg : Submodule.FG Λ)
    (hden : ∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) (X : Matrix n n A) :
    ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ := by
  classical
  obtain ⟨t, rfl⟩ := hfg
  choose f hf1 hf using fun v : n → A => hden (X *ᵥ v)
  refine ⟨∏ v ∈ t, f v, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ => by have := hf1 v; omega)
  · intro y hy
    rw [Nat.cast_smul_eq_nsmul A]
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase t f hx, mul_nsmul, ← Nat.cast_smul_eq_nsmul A (f x)]
      exact Submodule.smul_of_tower_mem _ (∏ v ∈ t.erase x, f v) (hf x)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Matrix.mulVec_add, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : X *ᵥ (a • x) = a • (X *ᵥ x) := by
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
      rw [this, smul_comm]
      exact Submodule.smul_mem _ a hx

/- English proof (translation)
Introduce `Λ hfg hden X` and use `finiteRing_sq_sub_mul_sq_eq_of_card Λ hfg hden X`.
-/
theorem main : ∀ {A : Type} [inst : CommRing A] {S : Subring A} {n : Type} [inst_1 : Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)), Submodule.FG Λ →
    (∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) →
    ∀ (X : Matrix n n A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ :=
  fun Λ hfg hden X => finiteRing_sq_sub_mul_sq_eq_of_card Λ hfg hden X

end GlobalTheory.SublatticeFacts
