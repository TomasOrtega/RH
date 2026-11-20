import Mathlib
import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.StatementI
open Formalism.FourierDecayAlt Finset

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun u u' l M₀ h => ?_, fun r => by nlinarith [Nat.zero_le r]⟩` and prove the remaining obligations. Establish `hmax : min (u l) (u' l) + 5 * (M₀ : ℝ) ≤ max (u l) (u' l)`. Use `max_sub_min_eq_abs (u l) (u' l)` as an intermediate fact. Rewrite `h` using `[abs_sub_comm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨(range M₀).image (fun i : ℕ => -(min (u l) (u' l) + 3 + 5 * (i : ℝ))), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[card_image_of_injective, card_range]`. Introduce `i j hij`. Establish `: (i : ℝ) = j`. Simplify using `only at hij`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Introduce `y hy y' hy' hne`. Take `⟨i, -, rfl⟩` from `mem_image.1 hy`. Take `⟨j, -, rfl⟩` from `mem_image.1 hy'`.

Establish `hij : i ≠ j` using `fun e => hne (by rw [e])`. Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases. Establish `: (i : ℝ) + 1 ≤ j` using `by exact_mod_cast hlt`. Conclude with `le_trans (by linarith) (le_abs_self _)`. Establish `: (j : ℝ) + 1 ≤ i` using `by exact_mod_cast hlt`.

Conclude with `le_trans (by linarith) (neg_le_abs _)`. Introduce `y hy`. Take `⟨i, hi, rfl⟩` from `mem_image.1 hy`. Establish `h1 : (i : ℝ) + 1 ≤ M₀` using `by exact_mod_cast mem_range.1 hi`. Establish `h0 : (0 : ℝ) ≤ i` using `Nat.cast_nonneg i`.

Unfold `I.OnCut`. Break down `le_total (u l) (u' l) with hle | hle` into its components or cases. Rewrite `hmax` using `[min_eq_left hle, max_eq_right hle]`. Rewrite using `[min_eq_left hle]`. Conclude with `⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩`.

Rewrite `hmax` using `[min_eq_right hle, max_eq_left hle]`. Rewrite using `[min_eq_right hle]`. Conclude with `⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩`.
-/
theorem exists_grid_five_apart_on_cut :
    (∀ (u u' : ℕ → ℝ) (l M₀ : ℕ), 5 * (M₀ : ℝ) ≤ |u l - u' l| → ∃ Y : Finset ℝ, M₀ ≤ Y.card ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧
      ∀ y ∈ Y, I.OnCut u u' l y ∧ I.OnCut u u' l (y + 1)) ∧
    ∀ r : ℕ, 5 * (3 * (r + 1) * (2 * r + 1)) ≤ 30 * (r + 1) ^ 2 + 6 := by
  refine ⟨fun u u' l M₀ h => ?_, fun r => by nlinarith [Nat.zero_le r]⟩
  have hmax : min (u l) (u' l) + 5 * (M₀ : ℝ) ≤ max (u l) (u' l) := by
    have := max_sub_min_eq_abs (u l) (u' l)
    rw [abs_sub_comm] at h
    linarith
  refine ⟨(range M₀).image (fun i : ℕ => -(min (u l) (u' l) + 3 + 5 * (i : ℝ))), ?_, ?_, ?_⟩
  · rw [card_image_of_injective, card_range]
    intro i j hij
    have : (i : ℝ) = j := by
      simp only at hij
      linarith
    exact_mod_cast this
  · intro y hy y' hy' hne
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy'
    have hij : i ≠ j := fun e => hne (by rw [e])
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      exact le_trans (by linarith) (le_abs_self _)
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      exact le_trans (by linarith) (neg_le_abs _)
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
    have h1 : (i : ℝ) + 1 ≤ M₀ := by exact_mod_cast mem_range.1 hi
    have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    unfold I.OnCut
    rcases le_total (u l) (u' l) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hmax
      rw [min_eq_left hle]
      exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
    · rw [min_eq_right hle, max_eq_left hle] at hmax
      rw [min_eq_right hle]
      exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩

end GlobalTheory
