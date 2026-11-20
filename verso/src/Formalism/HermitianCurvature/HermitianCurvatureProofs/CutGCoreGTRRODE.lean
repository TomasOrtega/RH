import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
Introduce `ι _ _ Mf Bm h0 hadd hper hd hoff`. Establish `hderiv : ∀ (φ : ℝ) (i j : ι), HasDerivAt (fun x => Mf x i j) (Bm i i * Mf φ i j) φ`. Introduce `φ i j`. Establish `hg0` using `HasDerivAt.sum (u := Finset.univ) (fun k _ => (hd i k).mul_const (Mf φ k j))`. Establish `ef : (∑ k : ι, fun (y : ℝ) => Mf y i k * Mf φ k j) = fun h : ℝ => ∑ k, Mf h i k * Mf φ k j`.

Use function extensionality and compare the values at `h`. Rewrite using `[Finset.sum_apply]`. Rewrite `hg0` using `[ef]`. Establish `hsum : ∑ k, Bm i k * Mf φ k j = Bm i i * Mf φ i j`. Rewrite using `[Finset.sum_eq_single i]`.

Introduce `k _ hk`. Rewrite using `[hoff i k (Ne.symm hk), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Rewrite `hg0` using `[hsum]`.

Establish `h2` using `HasDerivAt.comp_sub_const φ φ (by rw [sub_self]; exact hg0)`. Establish `e : (fun x => Mf x i j) = fun x : ℝ => ∑ k, Mf (x - φ) i k * Mf φ k j`. Use function extensionality and compare the values at `x`. Rewrite using `[← Matrix.mul_apply, ← hadd, sub_add_cancel]`. Rewrite using `[e]`.

Conclude with `h2`. Establish `hsol : ∀ (i j : ι) (x : ℝ), Mf x i j = Complex.exp (Bm i i * x) * (if i = j then 1 else 0)`. Introduce `i j x`. Establish `hf : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y) * Mf y i j) 0 y`. Introduce `y`.

Establish `he : HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y)) (Complex.exp (-Bm i i * y) * (-Bm i i * 1)) y` using `(((hasDerivAt_id y).ofReal_comp).const_mul (-Bm i i)).cexp`. Establish `hm` using `he.mul (hderiv y i j)`. Establish `h3 : Complex.exp (-Bm i i * ↑y) * (-Bm i i * 1) * Mf y i j + Complex.exp (-Bm i i * ↑y) * (Bm i i * Mf y i j) = 0`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hm` using `[h3]`.

Conclude with `hm`. Establish `hc` using `is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt) (fun y => (hf y).deriv) x 0`. Simplify using `only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0, Matrix.one_apply] at hc`. Rewrite using `[← hc, ← mul_assoc, ← Complex.exp_add]`. Simplify using the standard rewrite rules.

Establish `hn : ∀ i, ∃ n : ℤ, Bm i i = n * Complex.I`. Introduce `i`. Establish `h1` using `hsol i i (2 * Real.pi)`. Rewrite `h1` using `[hper]`. Simplify using `only [Matrix.one_apply_eq, if_true, mul_one] at h1`.

Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h1.symm`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hpi : (2 * (Real.pi : ℂ)) ≠ 0`. Simplify using `[Real.pi_ne_zero]`. Apply `mul_right_cancel₀ hpi` to reduce the goal to its premises.

Move the coercions through the operations in `at hn`. Take the linear combination `hn`. Use `choose n hn using hn`. Use `⟨n, fun φ i j => ?_⟩` and prove the remaining obligations. Rewrite using `[hsol]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[hn]`. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules.
-/
theorem rotation_ode_holds : GTRRODE := by
  intro ι _ _ Mf Bm h0 hadd hper hd hoff
  have hderiv : ∀ (φ : ℝ) (i j : ι), HasDerivAt (fun x => Mf x i j) (Bm i i * Mf φ i j) φ := by
    intro φ i j
    have hg0 := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hd i k).mul_const (Mf φ k j))
    have ef : (∑ k : ι, fun (y : ℝ) => Mf y i k * Mf φ k j) = fun h : ℝ => ∑ k, Mf h i k * Mf φ k j := by
      funext h
      rw [Finset.sum_apply]
    rw [ef] at hg0
    have hsum : ∑ k, Bm i k * Mf φ k j = Bm i i * Mf φ i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hoff i k (Ne.symm hk), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum] at hg0
    have h2 := HasDerivAt.comp_sub_const φ φ (by rw [sub_self]; exact hg0)
    have e : (fun x => Mf x i j) = fun x : ℝ => ∑ k, Mf (x - φ) i k * Mf φ k j := by
      funext x
      rw [← Matrix.mul_apply, ← hadd, sub_add_cancel]
    rw [e]
    exact h2
  have hsol : ∀ (i j : ι) (x : ℝ), Mf x i j = Complex.exp (Bm i i * x) * (if i = j then 1 else 0) := by
    intro i j x
    have hf : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y) * Mf y i j) 0 y := by
      intro y
      have he : HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y)) (Complex.exp (-Bm i i * y) * (-Bm i i * 1)) y :=
        (((hasDerivAt_id y).ofReal_comp).const_mul (-Bm i i)).cexp
      have hm := he.mul (hderiv y i j)
      have h3 : Complex.exp (-Bm i i * ↑y) * (-Bm i i * 1) * Mf y i j + Complex.exp (-Bm i i * ↑y) * (Bm i i * Mf y i j) = 0 := by
        ring
      rw [h3] at hm
      exact hm
    have hc := is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt) (fun y => (hf y).deriv) x 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0, Matrix.one_apply] at hc
    rw [← hc, ← mul_assoc, ← Complex.exp_add]
    simp
  have hn : ∀ i, ∃ n : ℤ, Bm i i = n * Complex.I := by
    intro i
    have h1 := hsol i i (2 * Real.pi)
    rw [hper] at h1
    simp only [Matrix.one_apply_eq, if_true, mul_one] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1.symm
    refine ⟨n, ?_⟩
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  choose n hn using hn
  refine ⟨n, fun φ i j => ?_⟩
  rw [hsol]
  split_ifs with h
  · subst h
    rw [hn]
    ring_nf
  · simp

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
