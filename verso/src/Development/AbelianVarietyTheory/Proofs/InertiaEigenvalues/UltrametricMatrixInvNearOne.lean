import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ n _ _ X Z t ht0 ht1 hZX hX i j`. Establish `key : Z - 1 = -((X - 1) + (Z - 1) * (X - 1))`. Establish `h : (Z - 1) * (X - 1) = Z * X - Z - X + 1` using `by noncomm_ring`. Rewrite using `[h, hZX]`. Normalize the expressions using the abelian group laws.

Use `haveI : Nonempty (n × n) := ⟨(i, j)⟩`. Take `⟨⟨i0, j0⟩, hmax⟩` from `Finite.exists_max (fun p : n × n => ‖(Z - 1) p.1 p.2‖)`. Use `set s := ‖(Z - 1) i0 j0‖ with hs`. Establish `hbound : ∀ a b, ‖(Z - 1) a b‖ ≤ max t (s * t)`. Introduce `a b`.

Establish `hprod : ‖((Z - 1) * (X - 1)) a b‖ ≤ s * t`. Rewrite using `[Matrix.mul_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg (norm_nonneg _) ht0) fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hmax (a, k)) (hX k b) (norm_nonneg _) (norm_nonneg _)`.

Rewrite using `[key, Matrix.neg_apply, norm_neg, Matrix.add_apply]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hX a b) hprod)`. Establish `hs0 : 0 ≤ s` using `norm_nonneg _`. Establish `hst : s ≤ t`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `h1` using `hbound i0 j0`. Rewrite `h1` using `[← hs]`. Break down `le_max_iff.mp h1 with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `(hmax (i, j)).trans hst`.
-/
theorem matrix_inv_near_one : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n]
    [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 →
    (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by
  intro E _ _ n _ _ X Z t ht0 ht1 hZX hX i j
  have key : Z - 1 = -((X - 1) + (Z - 1) * (X - 1)) := by
    have h : (Z - 1) * (X - 1) = Z * X - Z - X + 1 := by noncomm_ring
    rw [h, hZX]; abel
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨i0, j0⟩, hmax⟩ := Finite.exists_max (fun p : n × n => ‖(Z - 1) p.1 p.2‖)
  set s := ‖(Z - 1) i0 j0‖ with hs
  have hbound : ∀ a b, ‖(Z - 1) a b‖ ≤ max t (s * t) := by
    intro a b
    have hprod : ‖((Z - 1) * (X - 1)) a b‖ ≤ s * t := by
      rw [Matrix.mul_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg (norm_nonneg _) ht0) fun k _ => ?_
      rw [norm_mul]
      exact mul_le_mul (hmax (a, k)) (hX k b) (norm_nonneg _) (norm_nonneg _)
    rw [key, Matrix.neg_apply, norm_neg, Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hX a b) hprod)
  have hs0 : 0 ≤ s := norm_nonneg _
  have hst : s ≤ t := by
    by_contra hlt
    push_neg at hlt
    have h1 := hbound i0 j0
    rw [← hs] at h1
    rcases le_max_iff.mp h1 with h | h
    · linarith
    · nlinarith
  exact (hmax (i, j)).trans hst

end GlobalTheory
