import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex ArithmeticFunction

noncomputable section

namespace Formalism.ZF

namespace VonMangoldtMertensInequality

/- English proof (translation)
Rewrite using `[LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, Complex.re_ofReal_mul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), Complex.exp_re]`. Establish `hre : (Complex.log (n : ℂ)).re = Real.log n`. Rewrite using `[Complex.log_re, Complex.norm_natCast]`. Establish `him : (Complex.log (n : ℂ)).im = 0`. Rewrite using `[Complex.log_im, Complex.natCast_arg]`.

Simplify using `only [Complex.mul_re, Complex.mul_im, hre, him, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]`. Rewrite using `[mul_assoc]`. Use `congr 2`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← Real.cos_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma re_term_vonMangoldt {n : ℕ} (hn : n ≠ 0) (σ y : ℝ) :
    (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re =
      Λ n * Real.exp (-σ * Real.log n) * Real.cos (y * Real.log n) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, Complex.re_ofReal_mul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), Complex.exp_re]
  have hre : (Complex.log (n : ℂ)).re = Real.log n := by
    rw [Complex.log_re, Complex.norm_natCast]
  have him : (Complex.log (n : ℂ)).im = 0 := by
    rw [Complex.log_im, Complex.natCast_arg]
  simp only [Complex.mul_re, Complex.mul_im, hre, him, Complex.neg_re, Complex.neg_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [mul_assoc]
  congr 2
  · congr 1
    ring
  · rw [← Real.cos_neg]
    congr 1
    ring

/- English proof (translation)
Establish `hs : 1 < ((σ : ℂ) + y * I).re` using `by simp [hσ]`. Establish `h1` using `(ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum`. Rewrite `h1` using `[ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div]`. Simplify `Complex.reCLM.hasSum h1` using `only [Complex.reCLM_apply]`.
-/
lemma hasSum_re_L {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    HasSum (fun n => (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re)
      (-(deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I))).re := by
  have hs : 1 < ((σ : ℂ) + y * I).re := by simp [hσ]
  have h1 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div] at h1
  simpa only [Complex.reCLM_apply] using Complex.reCLM.hasSum h1

/- English proof (translation)
Rewrite using `[Real.cos_two_mul]`. Use polynomial arithmetic with `[mul_nonneg ha (sq_nonneg (1 + Real.cos θ))]`.
-/
lemma comb_nonneg (a θ : ℝ) (ha : 0 ≤ a) :
    0 ≤ 3 * a + 4 * (a * Real.cos θ) + a * Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [mul_nonneg ha (sq_nonneg (1 + Real.cos θ))]

end VonMangoldtMertensInequality

open VonMangoldtMertensInequality in
/- English proof (translation)
Introduce `σ t hσ`. Establish `h0` using `hasSum_re_L hσ 0`. Establish `h1` using `hasSum_re_L hσ t`. Establish `h2` using `hasSum_re_L hσ (2 * t)`. Establish `hs` using `((h0.mul_left 3).add (h1.mul_left 4)).add h2`.

Establish `key` using `HasSum.nonneg (fun n => ?_) hs`. Establish `e0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = σ` using `by simp`. Establish `e2 : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = σ + 2 * t * I` using `by push_cast; ring`. Rewrite `key` using `[e0, e2]`. Conclude with `key`.

Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Simplify using `[LSeries.term_zero]`. Rewrite using `[re_term_vonMangoldt hn, re_term_vonMangoldt hn, re_term_vonMangoldt hn]`. Establish `ha : 0 ≤ Λ n * Real.exp (-σ * Real.log n)` using `mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le`.

Establish `hc` using `comb_nonneg _ (t * Real.log n) ha`. Rewrite using `[zero_mul, Real.cos_zero, mul_one, show 2 * t * Real.log n = 2 * (t * Real.log n) by ring]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mertensInequality : ThreeFourOne := by
  intro σ t hσ
  have h0 := hasSum_re_L hσ 0
  have h1 := hasSum_re_L hσ t
  have h2 := hasSum_re_L hσ (2 * t)
  have hs := ((h0.mul_left 3).add (h1.mul_left 4)).add h2
  have key := HasSum.nonneg (fun n => ?_) hs
  · have e0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = σ := by simp
    have e2 : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = σ + 2 * t * I := by push_cast; ring
    rw [e0, e2] at key
    exact key
  · by_cases hn : n = 0
    · subst hn
      simp [LSeries.term_zero]
    · rw [re_term_vonMangoldt hn, re_term_vonMangoldt hn, re_term_vonMangoldt hn]
      have ha : 0 ≤ Λ n * Real.exp (-σ * Real.log n) :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
      have hc := comb_nonneg _ (t * Real.log n) ha
      rw [zero_mul, Real.cos_zero, mul_one, show 2 * t * Real.log n = 2 * (t * Real.log n) by ring]
      linarith

end Formalism.ZF
