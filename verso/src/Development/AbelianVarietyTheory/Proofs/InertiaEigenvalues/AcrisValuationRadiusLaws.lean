import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocyclePartialSumIterateSuccStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Conclude with `(Fact.out : l.Prime).one_lt` after adjusting the coercions.
-/
lemma vrlaw_one_lt : (1 : ℝ) < l := by
  exact_mod_cast (Fact.out : l.Prime).one_lt

/- English proof (translation)
Establish `hl` using `vrlaw_one_lt l`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Real.rpow_neg_one]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hl.le (by linarith)`. Conclude with `Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)`.
-/
lemma vrlaw_rad (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hl := vrlaw_one_lt l
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hl.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)

/- English proof (translation)
Establish `hG` using `isGauss_gC_target l ρ h0 h1`. Establish `hm` using `hG.2.2.2.1 0 (l : Formalism.Per.Acris l)`. Rewrite `hm` using `[zero_mul, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1]`. Establish `: gC l ρ 0 * (1 - ρ) = 0` using `by linarith`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h (by linarith)`.
-/
lemma vrlaw_gC_zero (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : gC l ρ 0 = 0 := by
  have hG := isGauss_gC_target l ρ h0 h1
  have hm := hG.2.2.2.1 0 (l : Formalism.Per.Acris l)
  rw [zero_mul, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1] at hm
  have : gC l ρ 0 * (1 - ρ) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h (by linarith)

/- English proof (translation)
Introduce `l _ r hr0 hr1`. Establish `hl` using `vrlaw_one_lt l`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Take `⟨hρ0, hρ1⟩` from `vrlaw_rad l r hr0 hr1`. Use `set ρ : ℝ := (l : ℝ) ^ (-r) with hρ`.

Establish `hG` using `isGauss_gC_target l ρ hρ0 hρ1`. Establish `hpos : ∀ x : Formalism.Per.Acris l, x ≠ 0 → 0 < gC l ρ x` using `fun x hx => GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ hρ0 hρ1`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hx hy`. Simplify using `only [vr]`.

Rewrite using `[← hρ, hG.2.2.2.1 x y, Real.logb_mul (hpos x hx).ne' (hpos y hy).ne']`. Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`. Establish `hl' : (0 : ℝ) < l` using `hl0`. Establish `hrl0 : 0 < r / l` using `div_pos hr0 hl'`.

Establish `hrl1 : r / l ≤ 1`. Rewrite using `[div_le_one hl']`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hσ0, hσ1⟩` from `vrlaw_rad l (r / l) hrl0 hrl1`. Establish `he : ρ ^ ((1 : ℝ) / l) = (l : ℝ) ^ (-(r / l))`.

Rewrite using `[hρ, ← Real.rpow_mul hl0.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hF` using `GlobalTheory.T.gaussNormAcris_frobenius_eq_pow_root_radius l ρ hρ0 hρ1 x`. Rewrite `hF` using `[he]`.

Establish `hxp : 0 < gC l ((l : ℝ) ^ (-(r / l))) x` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ hσ0 hσ1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Rewrite `hF` using `[h0, vrlaw_gC_zero l ρ hρ0 hρ1]`. Conclude with `(pow_pos hxp l).ne' hF.symm`.

Simplify using `only [vr]`. Rewrite using `[← hρ, hF, Real.logb_pow]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x n hx`. Establish `hpow : ∀ m : ℕ, gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', mul_assoc, hG.2.2.2.1, ih, (GlobalTheory.T.gaussNormAcris_basic_values l ρ hρ0 hρ1).2.1]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [vr]`. Rewrite using `[← hρ, hpow n, Real.logb_mul (pow_pos (by rw [hρ]; exact Real.rpow_pos_of_pos hl0 _) n).ne' (hpos x hx).ne', Real.logb_pow, hρ, Real.logb_rpow hl0 hl.ne']`. Expand and normalize the polynomial expressions, which then agree. Introduce `x _`.

Both sides reduce to the same expression.
-/
theorem vr_laws : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), 0 < r → r ≤ 1 →
    (∀ x y : Formalism.Per.Acris l, x ≠ 0 → y ≠ 0 → vr l r (x * y) = vr l r x + vr l r y) ∧
    (∀ x : Formalism.Per.Acris l, x ≠ 0 → φc l x ≠ 0 ∧ vr l r (φc l x) = l * vr l (r / l) x) ∧
    (∀ (x : Formalism.Per.Acris l) (n : ℕ), x ≠ 0 → vr l r ((l : Formalism.Per.Acris l) ^ n * x) = n * r + vr l r x) ∧
    ∀ x : Formalism.Per.Acris l, x ≠ 0 → vr l r x = -Real.logb l (gC l ((l : ℝ) ^ (-r)) x) := by
  intro l _ r hr0 hr1
  have hl := vrlaw_one_lt l
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hρ0, hρ1⟩ := vrlaw_rad l r hr0 hr1
  set ρ : ℝ := (l : ℝ) ^ (-r) with hρ
  have hG := isGauss_gC_target l ρ hρ0 hρ1
  have hpos : ∀ x : Formalism.Per.Acris l, x ≠ 0 → 0 < gC l ρ x := fun x hx => GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ hρ0 hρ1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    simp only [vr]
    rw [← hρ, hG.2.2.2.1 x y, Real.logb_mul (hpos x hx).ne' (hpos y hy).ne']
    ring
  · intro x hx
    have hl' : (0 : ℝ) < l := hl0
    have hrl0 : 0 < r / l := div_pos hr0 hl'
    have hrl1 : r / l ≤ 1 := by
      rw [div_le_one hl']; linarith
    obtain ⟨hσ0, hσ1⟩ := vrlaw_rad l (r / l) hrl0 hrl1
    have he : ρ ^ ((1 : ℝ) / l) = (l : ℝ) ^ (-(r / l)) := by
      rw [hρ, ← Real.rpow_mul hl0.le]
      congr 1
      ring
    have hF := GlobalTheory.T.gaussNormAcris_frobenius_eq_pow_root_radius l ρ hρ0 hρ1 x
    rw [he] at hF
    have hxp : 0 < gC l ((l : ℝ) ^ (-(r / l))) x := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ hσ0 hσ1
    refine ⟨?_, ?_⟩
    · intro h0
      rw [h0, vrlaw_gC_zero l ρ hρ0 hρ1] at hF
      exact (pow_pos hxp l).ne' hF.symm
    · simp only [vr]
      rw [← hρ, hF, Real.logb_pow]
      ring
  · intro x n hx
    have hpow : ∀ m : ℕ, gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', mul_assoc, hG.2.2.2.1, ih, (GlobalTheory.T.gaussNormAcris_basic_values l ρ hρ0 hρ1).2.1]
        ring
    simp only [vr]
    rw [← hρ, hpow n, Real.logb_mul (pow_pos (by rw [hρ]; exact Real.rpow_pos_of_pos hl0 _) n).ne' (hpos x hx).ne', Real.logb_pow,
      hρ, Real.logb_rpow hl0 hl.ne']
    ring
  · intro x _
    rfl

end GlobalTheory.PMon.Gauss

end
