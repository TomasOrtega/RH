import Mathlib

noncomputable section

open Matrix ComplexConjugate

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

def gamma (r : ℕ) (T T' : ℝ) (s : ℂ) : Matrix (Fin r ⊕ Fin 2) (Fin r ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks ((-2 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) 0 0 !![(-T : ℂ), s; conj s, (-T' : ℂ)]

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem binaryForm_mul_eq_normSq_add (T T' : ℝ) (s x y : ℂ) :
    T * (T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re) =
      Complex.normSq ((T : ℂ) * x - s * y) + (T * T' - Complex.normSq s) * Complex.normSq y := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem re_star_mul' (z w : ℂ) : (star z * w).re = z.re * w.re + z.im * w.im := by
  change ((starRingEnd ℂ) z * w).re = _
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Apply the first step, then apply the next step to every resulting obligation. Treat this case separately.

Apply the first step, then apply the next step to every resulting obligation. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Substitute using the available equality. Simplify using the standard rewrite rules.

Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis.

Prove the first alternative. Prove the second alternative. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
