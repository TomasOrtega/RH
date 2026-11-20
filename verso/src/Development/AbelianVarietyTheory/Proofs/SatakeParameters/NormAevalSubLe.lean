import Mathlib

namespace GlobalTheory.NormAevalSubBound

/- English proof (translation)
Establish `hadd : ∀ (a b : k) (r : ℝ), ‖a‖ ≤ r → ‖b‖ ≤ r → ‖a + b‖ ≤ r` using `fun a b r ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : ‖(a : k)‖ ≤ 1` using `IsUltrametricDist.norm_intCast_le_one k a`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using h`. Simplify using `using h`. Simplify using `using hδ`. Consider the case `add p q hp hq`. Take `⟨p1, p2, p3⟩` from `hp`.

Take `⟨q1, q2, q3⟩` from `hq`. Simplify using `only [map_add]`. Use `⟨hadd _ _ _ p1 q1, hadd _ _ _ p2 q2, ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_add_comm]`. Conclude with `hadd _ _ _ p3 q3`.

Consider the case `mul_X p j hp`. Take `⟨p1, p2, p3⟩` from `hp`. Simplify using `only [map_mul, MvPolynomial.aeval_X]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_one₀ p1 (norm_nonneg _) (hx j)`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ p2 (norm_nonneg _) (hy j)`. Establish `e : MvPolynomial.aeval x p * x j - MvPolynomial.aeval y p * y j = MvPolynomial.aeval x p * (x j - y j) + (MvPolynomial.aeval x p - MvPolynomial.aeval y p) * y j` using `by ring`. Rewrite using `[e]`.

Use `hadd _ _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) p1).trans (hxy j)`. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) (hy j)).trans p3`.
-/
theorem norm_aeval_sub_le {k : Type} [inst : NormedField k] [NormOneClass k] [IsUltrametricDist k]
    {J : Type} {x y : J → k} {δ : ℝ} (hδ : (0 : ℝ) ≤ δ) (hx : ∀ (j : J), ‖x j‖ ≤ (1 : ℝ))
    (hy : ∀ (j : J), ‖y j‖ ≤ (1 : ℝ)) (hxy : ∀ (j : J), ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖(MvPolynomial.aeval x : MvPolynomial J ℤ → k) P‖ ≤ (1 : ℝ) ∧
    ‖(MvPolynomial.aeval y : MvPolynomial J ℤ → k) P‖ ≤ (1 : ℝ) ∧
    ‖(MvPolynomial.aeval x : MvPolynomial J ℤ → k) P -
      (MvPolynomial.aeval y : MvPolynomial J ℤ → k) P‖ ≤ δ := by
  have hadd : ∀ (a b : k) (r : ℝ), ‖a‖ ≤ r → ‖b‖ ≤ r → ‖a + b‖ ≤ r := fun a b r ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : ‖(a : k)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one k a
    refine ⟨?_, ?_, ?_⟩
    · simpa using h
    · simpa using h
    · simpa using hδ
  | add p q hp hq =>
    obtain ⟨p1, p2, p3⟩ := hp
    obtain ⟨q1, q2, q3⟩ := hq
    simp only [map_add]
    refine ⟨hadd _ _ _ p1 q1, hadd _ _ _ p2 q2, ?_⟩
    rw [add_sub_add_comm]
    exact hadd _ _ _ p3 q3
  | mul_X p j hp =>
    obtain ⟨p1, p2, p3⟩ := hp
    simp only [map_mul, MvPolynomial.aeval_X]
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul]; exact mul_le_one₀ p1 (norm_nonneg _) (hx j)
    · rw [norm_mul]; exact mul_le_one₀ p2 (norm_nonneg _) (hy j)
    · have e : MvPolynomial.aeval x p * x j - MvPolynomial.aeval y p * y j =
          MvPolynomial.aeval x p * (x j - y j) +
            (MvPolynomial.aeval x p - MvPolynomial.aeval y p) * y j := by ring
      rw [e]
      refine hadd _ _ _ ?_ ?_
      · rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) p1).trans (hxy j)
      · rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hy j)).trans p3

end GlobalTheory.NormAevalSubBound
