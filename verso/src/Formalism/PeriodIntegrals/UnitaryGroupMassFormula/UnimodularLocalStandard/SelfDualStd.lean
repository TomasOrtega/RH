import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RelIdxNeZeroOfLeLeft

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

/- English proof (translation)
Simplify using `only [PI.ULS.stdH, PI.ULS.matH, LinearMap.mk₂'ₛₗ_apply]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `j _ hj`. Simplify using `only [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hj), smul_eq_mul, mul_zero, zero_mul]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.
-/
lemma stdH_apply (L : PeriodPair) (m : Type*) [Fintype m] [DecidableEq m] (x y : m → ℂ) :
    stdH L m x y = (∑ i, x i * conj (y i)) * ((area L : ℝ) : ℂ)⁻¹ := by
  simp only [PI.ULS.stdH, PI.ULS.matH, LinearMap.mk₂'ₛₗ_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    ring
  · intro j _ hj
    simp only [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hj), smul_eq_mul, mul_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

def detD (L : PeriodPair) : ℝ := (conj L.ω₁ * L.ω₂).im

/- English proof (translation)
Simplify using `only [detD, Complex.mul_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem detD_eq_re_mul_im_sub (L : PeriodPair) :
    detD L = L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re := by
  simp only [detD, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Introduce `h`. Establish `h' : L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re = 0` using `by rw [← detD_eq_re_mul_im_sub]; exact h`. Establish `hi` using `LinearIndependent.pair_iff.mp L.indep`. Establish `key : ∀ s t : ℝ, s * L.ω₁.re + t * L.ω₂.re = 0 → s * L.ω₁.im + t * L.ω₂.im = 0 → s = 0 ∧ t = 0`. Introduce `s t h1 h2`.

Apply `hi` to reduce the goal to its premises. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨e1, e2⟩` from `key L.ω₂.im (-L.ω₁.im) (by linear_combination h') (by ring)`. Take `⟨f1, f2⟩` from `key L.ω₂.re (-L.ω₁.re) (by ring) (by linear_combination (-L.ω₂.re) * e2 + (-L.ω₁.re) * e1)`. Conclude with `one_ne_zero (key 1 0 (by linear_combination (-1 : ℝ) * f2) (by linear_combination (-1 : ℝ) * e2)).1`.
-/
lemma detD_ne (L : PeriodPair) : detD L ≠ 0 := by
  intro h
  have h' : L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re = 0 := by rw [← detD_eq_re_mul_im_sub]; exact h
  have hi := LinearIndependent.pair_iff.mp L.indep
  have key : ∀ s t : ℝ, s * L.ω₁.re + t * L.ω₂.re = 0 → s * L.ω₁.im + t * L.ω₂.im = 0 →
      s = 0 ∧ t = 0 := by
    intro s t h1 h2
    apply hi
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re]
      linarith
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im]
      linarith
  obtain ⟨e1, e2⟩ := key L.ω₂.im (-L.ω₁.im) (by linear_combination h') (by ring)
  obtain ⟨f1, f2⟩ := key L.ω₂.re (-L.ω₁.re) (by ring)
    (by linear_combination (-L.ω₂.re) * e2 + (-L.ω₁.re) * e1)
  exact one_ne_zero (key 1 0 (by linear_combination (-1 : ℝ) * f2)
    (by linear_combination (-1 : ℝ) * e2)).1

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma area_eq (L : PeriodPair) : area L = |detD L| := rfl

/- English proof (translation)
Rewrite using `[detD_eq_re_mul_im_sub]`. Simplify using `only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, Complex.conj_re, Complex.conj_im, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma im_mul_conj (L : PeriodPair) (p q r s : ℝ) :
    ((p • L.ω₁ + q • L.ω₂) * conj (r • L.ω₁ + s • L.ω₂)).im = (q * r - p * s) * detD L := by
  rw [detD_eq_re_mul_im_sub]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, Complex.conj_re, Complex.conj_im, smul_eq_mul]
  ring

/- English proof (translation)
Use `⟨L.basis.repr z 0, L.basis.repr z 1, ?_⟩` and prove the remaining obligations. Establish `h` using `L.basis.sum_repr z`. Rewrite `h` using `[Fin.sum_univ_two, L.basis_zero, L.basis_one]`. Conclude with `h.symm`.
-/
lemma coords (L : PeriodPair) (z : ℂ) : ∃ s t : ℝ, z = s • L.ω₁ + t • L.ω₂ := by
  refine ⟨L.basis.repr z 0, L.basis.repr z 1, ?_⟩
  have h := L.basis.sum_repr z
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
  exact h.symm

/- English proof (translation)
Establish `hD` using `detD_ne L`. Rewrite `h` using `[area_eq]`. Break down `abs_choice (detD L) with hA | hA` into its components or cases. Rewrite `h` using `[hA, mul_div_assoc, div_self hD, mul_one]`. Conclude with `⟨k, h⟩`.

Rewrite `h` using `[hA, mul_div_assoc, div_neg, div_self hD, mul_neg, mul_one]`. Conclude with `⟨-k, by push_cast; linarith⟩`.
-/
lemma int_of_div (L : PeriodPair) {t : ℝ} {k : ℤ} (h : t * detD L / area L = k) : ∃ j : ℤ, t = j := by
  have hD := detD_ne L
  rw [area_eq] at h
  rcases abs_choice (detD L) with hA | hA
  · rw [hA, mul_div_assoc, div_self hD, mul_one] at h
    exact ⟨k, h⟩
  · rw [hA, mul_div_assoc, div_neg, div_self hD, mul_neg, mul_one] at h
    exact ⟨-k, by push_cast; linarith⟩

/- English proof (translation)
Rewrite using `[PeriodPair.lattice, Submodule.mem_span_pair]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, h⟩`. Use `⟨p, q, ?_⟩` and prove the remaining obligations. Rewrite using `[← h]`.

Simplify using `[zsmul_eq_mul, Complex.real_smul]`. Introduce and unpack `⟨p, q, h⟩`. Use `⟨p, q, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Simplify using `[zsmul_eq_mul, Complex.real_smul]`.
-/
lemma lattice_iff (L : PeriodPair) (z : ℂ) : z ∈ L.lattice ↔ ∃ p q : ℤ, z = (p : ℝ) • L.ω₁ + (q : ℝ) • L.ω₂ := by
  rw [PeriodPair.lattice, Submodule.mem_span_pair]
  constructor
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [← h]
    simp [zsmul_eq_mul, Complex.real_smul]
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [h]
    simp [zsmul_eq_mul, Complex.real_smul]

end PI.UnitaryGroupMassFormula.UnimodLocStd
