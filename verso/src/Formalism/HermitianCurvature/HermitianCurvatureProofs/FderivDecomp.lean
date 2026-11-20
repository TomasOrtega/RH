import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtPrim

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

def wZ (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 - I * fderiv ℝ f ζ I)

def wZb (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 + I * fderiv ℝ f ζ I)

/- English proof (translation)
Take `⟨x, y, rfl⟩ : ∃ x y : ℝ, v = x + y * I` from `⟨v.re, v.im, (Complex.re_add_im v).symm⟩`. Establish `e : (x : ℂ) + y * I = x • (1 : ℂ) + y • I` using `by rw [Complex.real_smul, Complex.real_smul, mul_one]`. Establish `hL : L ((x : ℂ) + y * I) = (x : ℂ) * L 1 + (y : ℂ) * L I`. Rewrite using `[e, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]`. Rewrite using `[hL]`.

Simplify using `only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]`. Take the linear combination `((y : ℂ) * L I) * Complex.I_sq`.
-/
theorem clm_decomp (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = (1 / 2 : ℂ) * (L 1 - I * L I) * v + (1 / 2 : ℂ) * (L 1 + I * L I) * (starRingEnd ℂ v) := by

  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, v = x + y * I := ⟨v.re, v.im, (Complex.re_add_im v).symm⟩
  have e : (x : ℂ) + y * I = x • (1 : ℂ) + y • I := by rw [Complex.real_smul, Complex.real_smul, mul_one]
  have hL : L ((x : ℂ) + y * I) = (x : ℂ) * L 1 + (y : ℂ) * L I := by
    rw [e, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [hL]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((y : ℂ) * L I) * Complex.I_sq

/- English proof (translation)
Unfold `wZ wZb`. Conclude with `clm_decomp _ v`.
-/
theorem fderiv_decomp (f : ℂ → ℂ) (ζ v : ℂ) :
    fderiv ℝ f ζ v = wZ f ζ * v + wZb f ζ * (starRingEnd ℂ v) := by
  unfold wZ wZb
  exact clm_decomp _ v

def Hh (TT : ℝ) : Set ℂ := {w | TT < Complex.normSq (Complex.exp w)}

/- English proof (translation)
Use `first`. Consider the case `rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]`. Consider the case `simp [Complex.normSq_eq_norm_sq, Complex.norm_exp]`.
-/
theorem normSq_exp (w : ℂ) : Complex.normSq (Complex.exp w) = Real.exp w.re ^ 2 := by

  first
    | rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    | simp [Complex.normSq_eq_norm_sq, Complex.norm_exp]

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)`.
-/
theorem isOpen_Hh (TT : ℝ) : IsOpen (Hh TT) := isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)

/- English proof (translation)
Introduce `w1 h1 w2 h2 a b ha hb hab`. Simplify using `only [Hh, Set.mem_setOf_eq, normSq_exp] at h1 h2 ⊢`. Establish `hre : (a • w1 + b • w2).re = a * w1.re + b * w2.re` using `by simp`. Rewrite using `[hre]`. Break down `le_total w1.re w2.re with h | h` into its components or cases.

Combine the equalities or inequalities in the displayed calculation. Establish `e : a * w1.re + b * w2.re - w1.re = b * (w2.re - w1.re)`. Rewrite using `[show a = 1 - b by linarith]; ring`. Establish `: w1.re ≤ a * w1.re + b * w2.re` using `by nlinarith [mul_nonneg hb (sub_nonneg.2 h)]`. Use `gcongr`.

Combine the equalities or inequalities in the displayed calculation. Establish `e : a * w1.re + b * w2.re - w2.re = a * (w1.re - w2.re)`. Rewrite using `[show b = 1 - a by linarith]; ring`. Establish `: w2.re ≤ a * w1.re + b * w2.re` using `by nlinarith [mul_nonneg ha (sub_nonneg.2 h)]`. Use `gcongr`.
-/
theorem convex_Hh (TT : ℝ) : Convex ℝ (Hh TT) := by

  intro w1 h1 w2 h2 a b ha hb hab
  simp only [Hh, Set.mem_setOf_eq, normSq_exp] at h1 h2 ⊢
  have hre : (a • w1 + b • w2).re = a * w1.re + b * w2.re := by simp
  rw [hre]
  rcases le_total w1.re w2.re with h | h
  · calc TT < Real.exp w1.re ^ 2 := h1
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w1.re = b * (w2.re - w1.re) := by
          rw [show a = 1 - b by linarith]; ring
        have : w1.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
        gcongr
  · calc TT < Real.exp w2.re ^ 2 := h2
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w2.re = a * (w1.re - w2.re) := by
          rw [show b = 1 - a by linarith]; ring
        have : w2.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg ha (sub_nonneg.2 h)]
        gcongr

/- English proof (translation)
Simplify using `only [Hh, Set.mem_setOf_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]`.
-/
theorem Hh_add_period (TT : ℝ) (w : ℂ) (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by

  simp only [Hh, Set.mem_setOf_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

def bet (α : ℂ → ℂ) (w : ℂ) : ℂ := α (Complex.exp w) * Complex.exp w

def omL : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

/- English proof (translation)
Simplify using `[omL]`.
-/
theorem omL_apply (c v : ℂ) : omL c v = 2 * (c * v).im := by

  simp [omL]

def om (α : ℂ → ℂ) (w : ℂ) : ℂ →L[ℝ] ℝ := omL (bet α w)

/- English proof (translation)
The claim follows from `omL_apply _ _`.
-/
theorem om_apply (α : ℂ → ℂ) (w v : ℂ) : om α w v = 2 * (bet α w * v).im := omL_apply _ _

/- English proof (translation)
Simplify using `only [bet, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]`.
-/
theorem bet_periodic (α : ℂ → ℂ) (w : ℂ) (k : ℤ) : bet α (w + (k : ℂ) * (2 * Real.pi * I)) = bet α w := by

  simp only [bet, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
