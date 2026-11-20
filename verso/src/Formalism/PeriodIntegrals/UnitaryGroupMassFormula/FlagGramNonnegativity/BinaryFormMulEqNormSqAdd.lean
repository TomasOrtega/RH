import Mathlib

noncomputable section

open Matrix ComplexConjugate

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

def gamma (r : ℕ) (T T' : ℝ) (s : ℂ) : Matrix (Fin r ⊕ Fin 2) (Fin r ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks ((-2 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) 0 0 !![(-T : ℂ), s; conj s, (-T' : ℂ)]

/- English proof (translation)
Simplify using `only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem binaryForm_mul_eq_normSq_add (T T' : ℝ) (s x y : ℂ) :
    T * (T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re) =
      Complex.normSq ((T : ℂ) * x - s * y) + (T * T' - Complex.normSq s) * Complex.normSq y := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((starRingEnd ℂ) z * w).re = _`. Rewrite using `[Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem re_star_mul' (z w : ℂ) : (star z * w).re = z.re * w.re + z.im * w.im := by
  change ((starRingEnd ℂ) z * w).re = _
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Establish `hinl : ∀ a, (gamma r T T' s *ᵥ c) (Sum.inl a) = -(c (Sum.inl a) + c (Sum.inl a))`. Introduce `a`. Use `first`. Consider the case `(rw [gamma, Matrix.fromBlocks_mulVec]`. Apply the tactic sequence `simp [Matrix.smul_mulVec_assoc, Matrix.one_mulVec] <;> ring1)`.

Consider the case `(rw [gamma, Matrix.fromBlocks_mulVec]`. Apply the tactic sequence `simp [Matrix.smul_mulVec, Matrix.one_mulVec] <;> ring1)`. Consider the case `(simp [gamma, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq] <;> ring1)`. Consider the case `(simp [gamma, Matrix.mulVec, Matrix.dotProduct, Fintype.sum_sum_type, Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq] <;> ring1)`. Establish `hinr0 : (gamma r T T' s *ᵥ c) (Sum.inr 0) = -(T : ℂ) * c (Sum.inr 0) + s * c (Sum.inr 1)`.

Rewrite using `[gamma, Matrix.fromBlocks_mulVec]`. Simplify using `[dotProduct, Fin.sum_univ_two]`. Establish `hinr1 : (gamma r T T' s *ᵥ c) (Sum.inr 1) = conj s * c (Sum.inr 0) + -(T' : ℂ) * c (Sum.inr 1)`. Rewrite using `[gamma, Matrix.fromBlocks_mulVec]`. Simplify using `[dotProduct, Fin.sum_univ_two]`.

Establish `hsplit : star c ⬝ᵥ (gamma r T T' s *ᵥ c) = ∑ a, star (c (Sum.inl a)) * (gamma r T T' s *ᵥ c) (Sum.inl a) + (star (c (Sum.inr 0)) * (gamma r T T' s *ᵥ c) (Sum.inr 0) + star (c (Sum.inr 1)) * (gamma r T T' s *ᵥ c) (Sum.inr 1))`. Simplify using `only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.star_apply]`. Establish `hsum : (∑ a, star (c (Sum.inl a)) * -(c (Sum.inl a) + c (Sum.inl a))).re = -2 * ∑ a, Complex.normSq (c (Sum.inl a))`. Rewrite using `[Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations.

Rewrite using `[re_star_mul', Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Simplify using `only [hinl, hinr0, hinr1]`. Simplify using `only [Complex.add_re, hsum, re_star_mul']`.

Simplify using `only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gamma_form (r : ℕ) (T T' : ℝ) (s : ℂ) (c : Fin r ⊕ Fin 2 → ℂ) :
    (star c ⬝ᵥ (gamma r T T' s *ᵥ c)).re =
      -2 * ∑ a, Complex.normSq (c (Sum.inl a)) -
        (T * Complex.normSq (c (Sum.inr 0)) + T' * Complex.normSq (c (Sum.inr 1)) -
          2 * (conj (c (Sum.inr 0)) * s * c (Sum.inr 1)).re) := by
  have hinl : ∀ a, (gamma r T T' s *ᵥ c) (Sum.inl a) =
      -(c (Sum.inl a) + c (Sum.inl a)) := by
    intro a
    first
    | (rw [gamma, Matrix.fromBlocks_mulVec]
       simp [Matrix.smul_mulVec_assoc, Matrix.one_mulVec] <;> ring1)
    | (rw [gamma, Matrix.fromBlocks_mulVec]
       simp [Matrix.smul_mulVec, Matrix.one_mulVec] <;> ring1)
    | (simp [gamma, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply,
        mul_ite, ite_mul, Finset.sum_ite_eq] <;> ring1)
    | (simp [gamma, Matrix.mulVec, Matrix.dotProduct, Fintype.sum_sum_type,
        Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq] <;> ring1)
  have hinr0 : (gamma r T T' s *ᵥ c) (Sum.inr 0) =
      -(T : ℂ) * c (Sum.inr 0) + s * c (Sum.inr 1) := by
    rw [gamma, Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fin.sum_univ_two]
  have hinr1 : (gamma r T T' s *ᵥ c) (Sum.inr 1) =
      conj s * c (Sum.inr 0) + -(T' : ℂ) * c (Sum.inr 1) := by
    rw [gamma, Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fin.sum_univ_two]
  have hsplit : star c ⬝ᵥ (gamma r T T' s *ᵥ c) =
      ∑ a, star (c (Sum.inl a)) * (gamma r T T' s *ᵥ c) (Sum.inl a) +
        (star (c (Sum.inr 0)) * (gamma r T T' s *ᵥ c) (Sum.inr 0) +
          star (c (Sum.inr 1)) * (gamma r T T' s *ᵥ c) (Sum.inr 1)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.star_apply]
  have hsum : (∑ a, star (c (Sum.inl a)) * -(c (Sum.inl a) + c (Sum.inl a))).re =
      -2 * ∑ a, Complex.normSq (c (Sum.inl a)) := by
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [re_star_mul', Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
      Complex.normSq_apply]
    ring
  rw [hsplit]
  simp only [hinl, hinr0, hinr1]
  simp only [Complex.add_re, hsum, re_star_mul']
  simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/- English proof (translation)
Rewrite using `[gamma_form]`. Establish `hS : 0 ≤ ∑ a, Complex.normSq (c (Sum.inl a))` using `Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)`. Establish `hd : 0 < T * T' - Complex.normSq s` using `by linarith`. Establish `hq : ∀ x y : ℂ, 0 ≤ T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re`. Introduce `x y`.

Establish `h` using `binaryForm_mul_eq_normSq_add T T' s x y`. Establish `h0 : 0 ≤ Complex.normSq ((T : ℂ) * x - s * y) + (T * T' - Complex.normSq s) * Complex.normSq y` using `add_nonneg (Complex.normSq_nonneg _) (mul_nonneg hd.le (Complex.normSq_nonneg _))`. Use the polynomial consequences of the given equalities and inequalities. Establish `hqpos : ∀ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) → 0 < T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re`. Introduce `x y hxy`.

Distinguish the cases in `hy : y = 0`. Establish `hx : x ≠ 0` using `hxy.resolve_right (not_not.mpr hy)`. Establish `hnx : 0 < Complex.normSq x` using `Complex.normSq_pos.mpr hx`. Substitute `hy` using the available equality. Simplify using `only [mul_zero, sub_zero, add_zero, Complex.zero_re, Complex.normSq_zero]`.

Use polynomial arithmetic with `[mul_pos hT hnx]`. Establish `h` using `binaryForm_mul_eq_normSq_add T T' s x y`. Establish `hny : 0 < Complex.normSq y` using `Complex.normSq_pos.mpr hy`. Establish `h0 : 0 < Complex.normSq ((T : ℂ) * x - s * y) + (T * T' - Complex.normSq s) * Complex.normSq y` using `add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (mul_pos hd hny)`. Use the polynomial consequences of the given equalities and inequalities.

Distinguish the cases in `hin : ∀ a, c (Sum.inl a) = 0`. Establish `hxy : c (Sum.inr 0) ≠ 0 ∨ c (Sum.inr 1) ≠ 0`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hc`. Simplify using `only [Pi.zero_apply] at hi`. Break down `i with a | ⟨_ | _ | k, hk⟩` into its components or cases.

Conclude with `absurd (hin a) hi`. Conclude with `Or.inl hi`. Conclude with `Or.inr hi`. Use linear arithmetic over natural numbers and integers. Use `hqpos _ _ hxy` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hin`. Take `⟨a, ha⟩` from `hin`. Establish `hpos : 0 < ∑ b, Complex.normSq (c (Sum.inl b))` using `Finset.sum_pos' (fun b _ => Complex.normSq_nonneg _) ⟨a, Finset.mem_univ _, Complex.normSq_pos.mpr ha⟩`. Use `hq (c (Sum.inr 0)) (c (Sum.inr 1))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gamma_neg (r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (s : ℂ)
    (hs : Complex.normSq s < T * T') (c : Fin r ⊕ Fin 2 → ℂ) (hc : c ≠ 0) :
    (star c ⬝ᵥ (gamma r T T' s *ᵥ c)).re < 0 := by
  rw [gamma_form]
  have hS : 0 ≤ ∑ a, Complex.normSq (c (Sum.inl a)) :=
    Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)
  have hd : 0 < T * T' - Complex.normSq s := by linarith
  have hq : ∀ x y : ℂ,
      0 ≤ T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re := by
    intro x y
    have h := binaryForm_mul_eq_normSq_add T T' s x y
    have h0 : 0 ≤ Complex.normSq ((T : ℂ) * x - s * y) +
        (T * T' - Complex.normSq s) * Complex.normSq y :=
      add_nonneg (Complex.normSq_nonneg _) (mul_nonneg hd.le (Complex.normSq_nonneg _))
    nlinarith
  have hqpos : ∀ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) →
      0 < T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re := by
    intro x y hxy
    by_cases hy : y = 0
    · have hx : x ≠ 0 := hxy.resolve_right (not_not.mpr hy)
      have hnx : 0 < Complex.normSq x := Complex.normSq_pos.mpr hx
      subst hy
      simp only [mul_zero, sub_zero, add_zero, Complex.zero_re, Complex.normSq_zero]
      nlinarith [mul_pos hT hnx]
    · have h := binaryForm_mul_eq_normSq_add T T' s x y
      have hny : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
      have h0 : 0 < Complex.normSq ((T : ℂ) * x - s * y) +
          (T * T' - Complex.normSq s) * Complex.normSq y :=
        add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (mul_pos hd hny)
      nlinarith
  by_cases hin : ∀ a, c (Sum.inl a) = 0
  · have hxy : c (Sum.inr 0) ≠ 0 ∨ c (Sum.inr 1) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
      simp only [Pi.zero_apply] at hi
      rcases i with a | ⟨_ | _ | k, hk⟩
      · exact absurd (hin a) hi
      · exact Or.inl hi
      · exact Or.inr hi
      · omega
    have := hqpos _ _ hxy
    linarith
  · push_neg at hin
    obtain ⟨a, ha⟩ := hin
    have hpos : 0 < ∑ b, Complex.normSq (c (Sum.inl b)) :=
      Finset.sum_pos' (fun b _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Complex.normSq_pos.mpr ha⟩
    have := hq (c (Sum.inr 0)) (c (Sum.inr 1))
    linarith

end PI.UnitaryGroupMassFormula.FlagGramNonneg
