import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace ThetaZeroHermitianLemmas

/- English proof (translation)
Simplify using `only [herm]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_add_left (L : PeriodPair) (x y w : ℂ) : herm L (x + y) w = herm L x w + herm L y w := by
  simp only [herm]; ring

/- English proof (translation)
Simplify using `only [herm, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_add_right (L : PeriodPair) (x y w : ℂ) : herm L w (x + y) = herm L w x + herm L w y := by
  simp only [herm, map_add]; ring

/- English proof (translation)
Simplify using `only [herm]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_neg_left (L : PeriodPair) (x w : ℂ) : herm L (-x) w = -herm L x w := by
  simp only [herm]; ring

/- English proof (translation)
Simplify using `[herm]`.
-/
lemma herm_zero_left (L : PeriodPair) (w : ℂ) : herm L 0 w = 0 := by
  simp [herm]

/- English proof (translation)
Simplify using `only [herm, map_div₀, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_half_right (L : PeriodPair) (x w : ℂ) : herm L x (w / 2) = herm L x w / 2 := by
  simp only [herm, map_div₀, map_ofNat]; ring

/- English proof (translation)
Simplify using `only [herm]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_half_left (L : PeriodPair) (x w : ℂ) : herm L (x / 2) w = herm L x w / 2 := by
  simp only [herm]; ring

/- English proof (translation)
Simplify using `only [herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_conj (L : PeriodPair) (x y : ℂ) : herm L x y = conj (herm L y x) := by
  simp only [herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]; ring

/- English proof (translation)
Rewrite using `[herm_conj L x y]`. Apply the tactic sequence `apply Complex.ext <;> simp [altE]`. Apply the tactic sequence `all_goals ring`.
-/
lemma herm_sub_swap (L : PeriodPair) (x y : ℂ) :
    herm L x y - herm L y x = -(2 * Complex.I * (altE L y x : ℂ)) := by
  rw [herm_conj L x y]
  apply Complex.ext <;> simp [altE]
  all_goals ring

/- English proof (translation)
Establish `h1 : Complex.exp (-(Real.pi : ℂ) * herm L z t - (Real.pi : ℂ) * herm L t t / 2) = Complex.exp (-(Real.pi : ℂ) * herm L z t) * Complex.exp (-((Real.pi : ℂ) * herm L t t / 2))`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Establish `h2 : Complex.exp (-(Real.pi : ℂ) * herm L 0 t - (Real.pi : ℂ) * herm L t t / 2) = Complex.exp (-((Real.pi : ℂ) * herm L t t / 2))`. Rewrite using `[herm_zero_left]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [th0, opU, zero_add, h1, h2]`. Rewrite using `[← mul_assoc, mul_div_mul_right _ _ (Complex.exp_ne_zero _)]`.
-/
lemma thetaZero_periodLattice_eq (L : PeriodPair) (t z : ℂ) :
    th0 L t z = sgStar L (z + t) * Complex.exp (-(Real.pi : ℂ) * herm L z t) / sgStar L t := by
  have h1 : Complex.exp (-(Real.pi : ℂ) * herm L z t - (Real.pi : ℂ) * herm L t t / 2)
      = Complex.exp (-(Real.pi : ℂ) * herm L z t) * Complex.exp (-((Real.pi : ℂ) * herm L t t / 2)) := by
    rw [← Complex.exp_add]; congr 1
  have h2 : Complex.exp (-(Real.pi : ℂ) * herm L 0 t - (Real.pi : ℂ) * herm L t t / 2)
      = Complex.exp (-((Real.pi : ℂ) * herm L t t / 2)) := by
    rw [herm_zero_left]; congr 1; ring
  simp only [th0, opU, zero_add, h1, h2]
  rw [← mul_assoc, mul_div_mul_right _ _ (Complex.exp_ne_zero _)]

/- English proof (translation)
Establish `h : Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1`. Rewrite using `[← Complex.exp_add]`. Use `Complex.exp_int_mul_two_pi_mul_I k using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Complex.exp_neg]`.

Conclude with `inv_eq_of_mul_eq_one_right h`.
-/
lemma exp_pi_int (k : ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (k : ℂ))) = Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) := by
  have h : Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_int_mul_two_pi_mul_I k using 2
    ring
  rw [Complex.exp_neg]
  exact inv_eq_of_mul_eq_one_right h

end ThetaZeroHermitianLemmas

open ThetaZeroHermitianLemmas

/- English proof (translation)
Introduce `L t`. Establish `h : opU L t (sgStar L) 0 = sgStar L t * Complex.exp (-(Real.pi : ℂ) * herm L t t / 2)`. Simplify using `only [opU, zero_add, herm_zero_left]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨h, fun ht => ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `mul_ne_zero (fun h0 => ht (((hb L).2.2.1 t).1 h0)) (Complex.exp_ne_zero _)`.
-/
theorem th0Const_of (hb : SgStarBasic) : ThetaZeroConstant := by
  intro L t
  have h : opU L t (sgStar L) 0 = sgStar L t * Complex.exp (-(Real.pi : ℂ) * herm L t t / 2) := by
    simp only [opU, zero_add, herm_zero_left]; congr 2; ring
  refine ⟨h, fun ht => ?_⟩
  rw [h]
  exact mul_ne_zero (fun h0 => ht (((hb L).2.2.1 t).1 h0)) (Complex.exp_ne_zero _)

/- English proof (translation)
Introduce `L t ω z hω ht`. Establish `hs : sgStar L t ≠ 0` using `fun h0 => ht (((hb L).2.2.1 t).1 h0)`. Apply the tactic sequence `have hc : semiChar L ω ≠ 0 := by unfold semiChar; split_ifs <;> norm_num`. Establish `key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2) * Complex.exp (-(Real.pi : ℂ) * herm L z (t + ω)) = Complex.exp (-(Real.pi : ℂ) * herm L z t) * Complex.exp ((Real.pi : ℂ) * herm L t ω + (Real.pi : ℂ) * herm L ω ω / 2)`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`.

Use `congr 1`. Rewrite using `[herm_add_left, herm_add_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[thetaZero_periodLattice_eq L (t + ω) z, thetaZero_periodLattice_eq L t z, ← add_assoc, hq L ω (z + t) hω, hq L ω t hω, div_eq_div_iff (mul_ne_zero (mul_ne_zero hc (Complex.exp_ne_zero _)) hs) hs]`. Take the linear combination `(semiChar L ω * sgStar L (z + t) * sgStar L t) * key`.
-/
theorem th0Class_of (hb : SgStarBasic) (hq : SgStarQuasi) : ThetaZeroClass := by
  intro L t ω z hω ht
  have hs : sgStar L t ≠ 0 := fun h0 => ht (((hb L).2.2.1 t).1 h0)
  have hc : semiChar L ω ≠ 0 := by unfold semiChar; split_ifs <;> norm_num
  have key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2)
        * Complex.exp (-(Real.pi : ℂ) * herm L z (t + ω))
      = Complex.exp (-(Real.pi : ℂ) * herm L z t)
        * Complex.exp ((Real.pi : ℂ) * herm L t ω + (Real.pi : ℂ) * herm L ω ω / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
    rw [herm_add_left, herm_add_right]; ring
  rw [thetaZero_periodLattice_eq L (t + ω) z, thetaZero_periodLattice_eq L t z, ← add_assoc, hq L ω (z + t) hω, hq L ω t hω,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hc (Complex.exp_ne_zero _)) hs) hs]
  linear_combination (semiChar L ω * sgStar L (z + t) * sgStar L t) * key

/- English proof (translation)
Introduce `L ω₀ hω hn`. Take `⟨t, rfl⟩ : ∃ t, ω₀ = t + t` from `⟨ω₀ / 2, by ring⟩`. Establish `h2 : (t + t) / 2 = t` using `by ring`. Rewrite `hn`, the goal using `[h2]`. Establish `hs : sgStar L t ≠ 0` using `fun h0 => hn (((hb L).2.2.1 t).1 h0)`.

Establish `hχ : semiChar L (t + t) = -1`. Rewrite using `[semiChar, if_neg (by rw [h2]; exact hn)]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hd` using `(hb L).1 show Differentiable ℂ (fun z => opU L t (sgStar L) z / opU L t (sgStar L) 0)`. Simplify using `only [opU, herm]`.

Use `fun_prop`. Simplify using `only [th0]`. Conclude with `div_self ((th0Const_of hb L t).2 hn)`. Introduce `z`. Rewrite using `[thetaZero_periodLattice_eq L t (-z), thetaZero_periodLattice_eq L t z]`.

Establish `h1 : sgStar L (-z + t) = -sgStar L (z - t)`. Rewrite using `[show -z + t = -(z - t) by ring]; exact (hb L).2.1 _`. Establish `h3` using `hq L (t + t) (z - t) hω`. Rewrite `h3` using `[show z - t + (t + t) = z + t by ring, hχ]`. Establish `key : Complex.exp (-(Real.pi : ℂ) * herm L (-z) t) = Complex.exp ((Real.pi : ℂ) * herm L (z - t) (t + t) + (Real.pi : ℂ) * herm L (t + t) (t + t) / 2) * Complex.exp (-(Real.pi : ℂ) * herm L z t)`.

Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Simplify using `only [herm, map_add, map_neg, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h3]`.

Take the linear combination `(-sgStar L (z - t) / sgStar L t) * key`. Introduce `z`. Rewrite using `[thetaZero_periodLattice_eq, div_eq_zero_iff, mul_eq_zero, (hb L).2.2.1]`. Simplify using `[Complex.exp_ne_zero, hs]`. Introduce `ω hω' z`.

Take `⟨k, hk⟩` from `hi L ω (t + t) hω' hω`. Establish `he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ)) = Complex.exp (-((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ)))`. Rewrite using `[hk]`. Use `push_cast`. Conclude with `(exp_pi_int k).symm`.

Establish `hsw` using `herm_sub_swap L (t + t) ω`. Establish `key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2) * Complex.exp (-(Real.pi : ℂ) * herm L (z + ω) t) = Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ)) * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * …`. Rewrite using `[he]`. Simplify using `only [← Complex.exp_add]`. Use `congr 1`.

Simplify using `only [herm, map_add] at hsw ⊢`. Take the linear combination `((Real.pi : ℂ) / 2) * hsw`. Rewrite using `[thetaZero_periodLattice_eq L t (z + ω), thetaZero_periodLattice_eq L t z, show z + ω + t = (z + t) + ω by ring, hq L ω (z + t) hω']`. Take the linear combination `(semiChar L ω * sgStar L (z + t) / sgStar L t) * key`.
-/
theorem th0Basic_of (hb : SgStarBasic) (hq : SgStarQuasi) (hi : AltEInt) : ThetaZeroBasic := by
  intro L ω₀ hω hn
  obtain ⟨t, rfl⟩ : ∃ t, ω₀ = t + t := ⟨ω₀ / 2, by ring⟩
  have h2 : (t + t) / 2 = t := by ring
  rw [h2] at hn ⊢
  have hs : sgStar L t ≠ 0 := fun h0 => hn (((hb L).2.2.1 t).1 h0)
  have hχ : semiChar L (t + t) = -1 := by
    rw [semiChar, if_neg (by rw [h2]; exact hn)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hd := (hb L).1
    show Differentiable ℂ (fun z => opU L t (sgStar L) z / opU L t (sgStar L) 0)
    simp only [opU, herm]
    fun_prop
  · simp only [th0]
    exact div_self ((th0Const_of hb L t).2 hn)
  · intro z
    rw [thetaZero_periodLattice_eq L t (-z), thetaZero_periodLattice_eq L t z]
    have h1 : sgStar L (-z + t) = -sgStar L (z - t) := by
      rw [show -z + t = -(z - t) by ring]; exact (hb L).2.1 _
    have h3 := hq L (t + t) (z - t) hω
    rw [show z - t + (t + t) = z + t by ring, hχ] at h3
    have key : Complex.exp (-(Real.pi : ℂ) * herm L (-z) t)
        = Complex.exp ((Real.pi : ℂ) * herm L (z - t) (t + t) + (Real.pi : ℂ) * herm L (t + t) (t + t) / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L z t) := by
      rw [← Complex.exp_add]; congr 1
      simp only [herm, map_add, map_neg, map_sub]; ring
    rw [h1, h3]
    linear_combination (-sgStar L (z - t) / sgStar L t) * key
  · intro z
    rw [thetaZero_periodLattice_eq, div_eq_zero_iff, mul_eq_zero, (hb L).2.2.1]
    simp [Complex.exp_ne_zero, hs]
  · intro ω hω' z
    obtain ⟨k, hk⟩ := hi L ω (t + t) hω' hω
    have he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))
        = Complex.exp (-((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))) := by
      rw [hk]; push_cast; exact (exp_pi_int k).symm
    have hsw := herm_sub_swap L (t + t) ω
    have key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L (z + ω) t)
        = Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))
          * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L z t) := by
      rw [he]; simp only [← Complex.exp_add]; congr 1
      simp only [herm, map_add] at hsw ⊢
      linear_combination ((Real.pi : ℂ) / 2) * hsw
    rw [thetaZero_periodLattice_eq L t (z + ω), thetaZero_periodLattice_eq L t z, show z + ω + t = (z + t) + ω by ring, hq L ω (z + t) hω']
    linear_combination (semiChar L ω * sgStar L (z + t) / sgStar L t) * key

/- English proof (translation)
Introduce `L ω₀ z hω hn hzt`. Take `⟨t, rfl⟩ : ∃ t, ω₀ = t + t` from `⟨ω₀ / 2, by ring⟩`. Establish `h2 : (t + t) / 2 = t` using `by ring`. Rewrite `hn`, `hzt`, the goal using `[h2]`. Establish `hζ : wZeta L t = s2 L * t + ((Real.pi : ℂ) / (area L : ℂ)) * conj t`.

Establish `h1` using `hzq L (t + t) (-t) hω (by rwa [neg_mem_iff])`. Rewrite `h1` using `[show -t + (t + t) = t by ring, hzo, he]`. Simplify using `only [map_add] at h1`. Take the linear combination `h1 / 2`. Establish `hd1 : HasDerivAt (fun w => wSigma L (w + t)) (wZeta L (z + t) * wSigma L (z + t)) z`.

Use `(hl L (z + t) hzt).comp z ((hasDerivAt_id' z).add_const t)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `this`. Establish `hg : HasDerivAt (fun w : ℂ => -(s2 L) * (w + t) ^ 2 / 2 + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2)) (-(s2 L) * (z + t) - (Real.pi : ℂ) * (conj t / (area L : ℂ))) z`. Establish `e1` using `((((hasDerivAt_id' z).add_const t).mul ((hasDerivAt_id' z).add_const t)).const_mul (-(s2 L))).div_const 2`.

Establish `e2` using `(((hasDerivAt_id' z).mul_const (conj t / (area L : ℂ))).const_mul (-(Real.pi : ℂ))).sub_const ((Real.pi : ℂ) * herm L t t / 2)`. Use `((e1.add e2).congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.mul_apply, herm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfull` using `(hd1.mul hg.cexp).div_const (opU L t (sgStar L) 0)`.

Establish `hfun : th0 L t = fun w => wSigma L (w + t) * Complex.exp (-(s2 L) * (w + t) ^ 2 / 2 + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2)) / opU L t (sgStar L) 0`. Use function extensionality and compare the values at `w`. Simplify using `only [th0]`. Use `congr 1`. Simplify using `only [opU, sgStar]`.

Rewrite using `[Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`. Use `hfull.congr_deriv ?_` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[hζ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem th0LogDeriv_of (hl : SigmaLogDeriv) (he : EtaSplit) (hzq : ZetaQuasi)
    (hzo : ZetaOdd) : ThetaZeroLogDerivative := by
  intro L ω₀ z hω hn hzt
  obtain ⟨t, rfl⟩ : ∃ t, ω₀ = t + t := ⟨ω₀ / 2, by ring⟩
  have h2 : (t + t) / 2 = t := by ring
  rw [h2] at hn hzt ⊢
  have hζ : wZeta L t = s2 L * t + ((Real.pi : ℂ) / (area L : ℂ)) * conj t := by
    have h1 := hzq L (t + t) (-t) hω (by rwa [neg_mem_iff])
    rw [show -t + (t + t) = t by ring, hzo, he] at h1
    simp only [map_add] at h1
    linear_combination h1 / 2
  have hd1 : HasDerivAt (fun w => wSigma L (w + t)) (wZeta L (z + t) * wSigma L (z + t)) z := by
    have := (hl L (z + t) hzt).comp z ((hasDerivAt_id' z).add_const t)
    rw [mul_one] at this
    exact this
  have hg : HasDerivAt (fun w : ℂ => -(s2 L) * (w + t) ^ 2 / 2
        + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2))
      (-(s2 L) * (z + t) - (Real.pi : ℂ) * (conj t / (area L : ℂ))) z := by
    have e1 := ((((hasDerivAt_id' z).add_const t).mul ((hasDerivAt_id' z).add_const t)).const_mul
      (-(s2 L))).div_const 2
    have e2 := (((hasDerivAt_id' z).mul_const (conj t / (area L : ℂ))).const_mul
      (-(Real.pi : ℂ))).sub_const ((Real.pi : ℂ) * herm L t t / 2)
    refine ((e1.add e2).congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply, Pi.mul_apply, herm]; ring
  have hfull := (hd1.mul hg.cexp).div_const (opU L t (sgStar L) 0)
  have hfun : th0 L t = fun w => wSigma L (w + t) * Complex.exp (-(s2 L) * (w + t) ^ 2 / 2
      + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2)) / opU L t (sgStar L) 0 := by
    funext w
    simp only [th0]
    congr 1
    simp only [opU, sgStar]
    rw [Complex.exp_add]; ring
  rw [hfun]
  refine hfull.congr_deriv ?_
  beta_reduce
  rw [hζ]; ring

end Formalism.L2.Th1.F
