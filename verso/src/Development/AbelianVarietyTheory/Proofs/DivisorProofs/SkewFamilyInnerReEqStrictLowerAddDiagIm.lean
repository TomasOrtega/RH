import Mathlib
open scoped ComplexConjugate

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ r s hs Y Y' hY hY'`. Use `set F : ι → Fin r → Fin r → ℝ := fun τ a b => (conj (Y (τ, a, b)) * Y' (τ, a, b)).re with hF`. Establish `key : ∀ τ a b, F τ b a = F τ a b`. Introduce `τ a b`. Establish `h2 : (s a * s b) * (s a * s b) = 1` using `by rw [mul_mul_mul_comm, hs, hs, one_mul]`.

Simplify using `only [hF, hY τ a b, hY' τ a b, map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.neg_im]`. Take the linear combination `((Y (τ, a, b)).re * (Y' (τ, a, b)).re + (Y (τ, a, b)).im * (Y' (τ, a, b)).im) * h2`. Establish `diag : ∀ τ a, F τ a a = (Y (τ, a, a)).im * (Y' (τ, a, a)).im`. Introduce `τ a`. Establish `h1` using `congrArg Complex.re (hY τ a a)`.

Establish `h2` using `congrArg Complex.re (hY' τ a a)`. Simplify using `only [hs, Complex.ofReal_one, Complex.neg_re, Complex.mul_re, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im, Complex.neg_im] at h1 h2`. Simplify using `only [hF, Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Establish `e1 : (Y (τ, a, a)).re = 0` using `by linarith`. Rewrite using `[e1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `per : ∀ τ, ∑ a, ∑ b, F τ a b = 2 * ∑ p : {p : Fin r × Fin r // p.2 < p.1}, F τ p.1.1 p.1.2 + ∑ a, F τ a a`. Introduce `τ`. Establish `hsplit : ∀ a b, F τ a b = ((if b < a then F τ a b else 0) + (if a < b then F τ a b else 0)) + (if a = b then F τ a b else 0)`. Introduce `a b`.

Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Simplify using `[h, not_lt_of_gt h, h.ne]`. Simplify using the standard rewrite rules. Simplify using `[h, not_lt_of_gt h, h.ne']`. Establish `hsub : ∑ p : {p : Fin r × Fin r // p.2 < p.1}, F τ p.1.1 p.1.2 = ∑ a, ∑ b, if b < a then F τ a b else 0`.

Rewrite using `[← Finset.sum_subtype (Finset.univ.filter (fun p : Fin r × Fin r => p.2 < p.1)) (by simp) (fun p : Fin r × Fin r => F τ p.1 p.2), Finset.sum_filter, Fintype.sum_prod_type]`. Establish `hsym : (∑ a, ∑ b, if a < b then F τ a b else 0) = ∑ a, ∑ b, if b < a then F τ a b else 0`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Rewrite using `[key]`.

Establish `hdiag : (∑ a, ∑ b, if a = b then F τ a b else 0) = ∑ a, F τ a a`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_add_distrib]`. Use `_ = _ := by rw [hsym, hdiag, hsub]; ring`.

Establish `lhs : ∑ p, (conj (Y p) * Y' p).re = ∑ τ, ∑ a, ∑ b, F τ a b`. Simplify using `only [hF, Fintype.sum_prod_type]`. Rewrite using `[lhs, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[per τ]`.

Simplify using `only [diag]`. Both sides reduce to the same expression.
-/
theorem skew_family_inner_re_split : ∀ {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ), (∀ a, s a * s a = 1) → ∀ (Y Y' : ι × Fin r × Fin r → ℂ), (∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b))) → (∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b))) → ∑ p, (conj (Y p) * Y' p).re = 2 * ∑ q : ι × {p : Fin r × Fin r // p.2 < p.1}, (conj (Y (q.1, q.2.1.1, q.2.1.2)) * Y' (q.1, q.2.1.1, q.2.1.2)).re + ∑ τ, ∑ a, (Y (τ, a, a)).im * (Y' (τ, a, a)).im := by
  intro ι _ r s hs Y Y' hY hY'
  set F : ι → Fin r → Fin r → ℝ := fun τ a b => (conj (Y (τ, a, b)) * Y' (τ, a, b)).re with hF
  have key : ∀ τ a b, F τ b a = F τ a b := by
    intro τ a b
    have h2 : (s a * s b) * (s a * s b) = 1 := by rw [mul_mul_mul_comm, hs, hs, one_mul]
    simp only [hF, hY τ a b, hY' τ a b, map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal,
      Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, Complex.neg_im]
    linear_combination ((Y (τ, a, b)).re * (Y' (τ, a, b)).re + (Y (τ, a, b)).im * (Y' (τ, a, b)).im) * h2
  have diag : ∀ τ a, F τ a a = (Y (τ, a, a)).im * (Y' (τ, a, a)).im := by
    intro τ a
    have h1 := congrArg Complex.re (hY τ a a)
    have h2 := congrArg Complex.re (hY' τ a a)
    simp only [hs, Complex.ofReal_one, Complex.neg_re, Complex.mul_re, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_im] at h1 h2
    simp only [hF, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have e1 : (Y (τ, a, a)).re = 0 := by linarith
    rw [e1]; ring
  have per : ∀ τ, ∑ a, ∑ b, F τ a b
      = 2 * ∑ p : {p : Fin r × Fin r // p.2 < p.1}, F τ p.1.1 p.1.2 + ∑ a, F τ a a := by
    intro τ
    have hsplit : ∀ a b, F τ a b = ((if b < a then F τ a b else 0) + (if a < b then F τ a b else 0))
        + (if a = b then F τ a b else 0) := by
      intro a b
      rcases lt_trichotomy a b with h | rfl | h
      · simp [h, not_lt_of_gt h, h.ne]
      · simp
      · simp [h, not_lt_of_gt h, h.ne']
    have hsub : ∑ p : {p : Fin r × Fin r // p.2 < p.1}, F τ p.1.1 p.1.2
        = ∑ a, ∑ b, if b < a then F τ a b else 0 := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin r × Fin r => p.2 < p.1)) (by simp)
        (fun p : Fin r × Fin r => F τ p.1 p.2), Finset.sum_filter, Fintype.sum_prod_type]
    have hsym : (∑ a, ∑ b, if a < b then F τ a b else 0) = ∑ a, ∑ b, if b < a then F τ a b else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [key]
    have hdiag : (∑ a, ∑ b, if a = b then F τ a b else 0) = ∑ a, F τ a a := by
      simp
    calc ∑ a, ∑ b, F τ a b
        = ∑ a, ∑ b, (((if b < a then F τ a b else 0) + (if a < b then F τ a b else 0))
            + (if a = b then F τ a b else 0)) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsplit a b))
      _ = ((∑ a, ∑ b, if b < a then F τ a b else 0) + (∑ a, ∑ b, if a < b then F τ a b else 0))
            + ∑ a, ∑ b, if a = b then F τ a b else 0 := by
          simp only [Finset.sum_add_distrib]
      _ = _ := by rw [hsym, hdiag, hsub]; ring
  have lhs : ∑ p, (conj (Y p) * Y' p).re = ∑ τ, ∑ a, ∑ b, F τ a b := by
    simp only [hF, Fintype.sum_prod_type]
  rw [lhs, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [per τ]
  simp only [diag]
  rfl

end GlobalTheory
