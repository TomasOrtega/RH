import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioProportionalTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmSubOneNeZeroPt

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.RatioTransport

open GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

/- English proof (translation)
Rewrite using `[T.frob, h, (GlobalTheory.PMon.Trans.acris_bcris l).2.1]`.
-/
theorem lift_phi {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) :
    T.eB (P.φB b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l y) := by
  rw [T.frob, h, (GlobalTheory.PMon.Trans.acris_bcris l).2.1]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact h`. Consider the case `succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']`. Conclude with `lift_phi T ih`.
-/
theorem lift_iter {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) (j : ℕ) :
    T.eB (P.φB^[j] b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((φc l)^[j] y) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact lift_phi T ih

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]`.
-/
theorem iter_lpow (m j : ℕ) (x : P.R.B) :
    P.φB^[m] ((l : P.R.B) ^ j * x) = (l : P.R.B) ^ j * P.φB^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

/- English proof (translation)
Establish `h : IsUnit (l : ℚ_[l])` using `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0).isUnit`. Establish `h2` using `h.map (algebraMap ℚ_[l] P.R.B)`. Rewrite `h2` using `[map_natCast]`. Conclude with `h2.pow m`.
-/
theorem isUnit_lpow (m : ℕ) : IsUnit ((l : P.R.B) ^ m) := by
  have h : IsUnit (l : ℚ_[l]) := (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0).isUnit
  have h2 := h.map (algebraMap ℚ_[l] P.R.B)
  rw [map_natCast] at h2
  exact h2.pow m

/- English proof (translation)
Take `⟨hinj, -, hz⟩` from `GlobalTheory.PMon.Trans.acris_bcris l`. Establish `e1 : (φc l)^[h] y = (l : Formalism.Per.Acris l) ^ s * y`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← lift_iter T hb, he, map_mul, map_pow, map_natCast, hb, map_mul, map_pow, map_natCast]`. Establish `e2 : (φc l)^[h] y' = (l : Formalism.Per.Acris l) ^ s * y'`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← lift_iter T hb', he', map_mul, map_pow, map_natCast, hb', map_mul, map_pow, map_natCast]`. Establish `e3 : y' ≠ 0`. Introduce and unpack `rfl`. Apply `h0` to reduce the goal to its premises.

Apply `T.eB.injective` to reduce the goal to its premises. Rewrite using `[hb', map_zero, map_zero]`. Establish `e4 : φc l y * y' = y * φc l y'`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← lift_phi T hb, ← lift_phi T hb', ← hb, ← hb', ← map_mul, ← map_mul, hr]`.

Take `⟨c, d, hc, hcd⟩` from `ratio_proportional_target l h s hs y y' e1 e2 e3 e4`. Establish `e5 : algebraMap ℚ_[l] P.R.B (c : ℚ_[l]) * b = algebraMap ℚ_[l] P.R.B (d : ℚ_[l]) * b'`. Apply `T.eB.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, T.zB, T.zB, hb, hb', ← hz, ← hz, ← map_mul, ← map_mul, hcd]`. Establish `hc' : (c : ℚ_[l]) ≠ 0` using `fun e => hc (Subtype.ext e)`.

Use `⟨(c : ℚ_[l])⁻¹ * d, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, mul_assoc, ← e5, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc', map_one, one_mul]`.
-/
theorem ratio_integral {h s : ℕ} (hs : s < h) {b b' : P.R.B} {y y' : Formalism.Per.Acris l}
    (hb : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y)
    (hb' : T.eB b' = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y')
    (he : P.φB^[h] b = (l : P.R.B) ^ s * b) (he' : P.φB^[h] b' = (l : P.R.B) ^ s * b')
    (h0 : b' ≠ 0) (hr : P.φB b * b' = b * P.φB b') : ∃ c : ℚ_[l], b = c • b' := by
  obtain ⟨hinj, -, hz⟩ := GlobalTheory.PMon.Trans.acris_bcris l
  have e1 : (φc l)^[h] y = (l : Formalism.Per.Acris l) ^ s * y := by
    apply hinj
    rw [← lift_iter T hb, he, map_mul, map_pow, map_natCast, hb, map_mul, map_pow, map_natCast]
  have e2 : (φc l)^[h] y' = (l : Formalism.Per.Acris l) ^ s * y' := by
    apply hinj
    rw [← lift_iter T hb', he', map_mul, map_pow, map_natCast, hb', map_mul, map_pow, map_natCast]
  have e3 : y' ≠ 0 := by
    rintro rfl
    apply h0
    apply T.eB.injective
    rw [hb', map_zero, map_zero]
  have e4 : φc l y * y' = y * φc l y' := by
    apply hinj
    rw [map_mul, map_mul, ← lift_phi T hb, ← lift_phi T hb', ← hb, ← hb', ← map_mul, ← map_mul, hr]
  obtain ⟨c, d, hc, hcd⟩ := ratio_proportional_target l h s hs y y' e1 e2 e3 e4
  have e5 : algebraMap ℚ_[l] P.R.B (c : ℚ_[l]) * b = algebraMap ℚ_[l] P.R.B (d : ℚ_[l]) * b' := by
    apply T.eB.injective
    rw [map_mul, map_mul, T.zB, T.zB, hb, hb', ← hz, ← hz, ← map_mul, ← map_mul, hcd]
  have hc' : (c : ℚ_[l]) ≠ 0 := fun e => hc (Subtype.ext e)
  refine ⟨(c : ℚ_[l])⁻¹ * d, ?_⟩
  rw [Algebra.smul_def, map_mul, mul_assoc, ← e5, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc', map_one, one_mul]

/- English proof (translation)
Introduce `l _ P AI T h s hs ω ω' hω hω' he he' h0 hr`. Take `⟨N, x, hx⟩` from `hω`. Take `⟨M, x', hx'⟩` from `hω'`. Establish `hb : T.eB ((l : P.R.B) ^ (N + M) * ω) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ M * x)`. Establish `e : (l : P.R.B) ^ (N + M) * ω = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * ω)` using `by ring`.

Rewrite using `[e, map_mul T.eB ((l : P.R.B) ^ M), hx]`. Simplify using `only [map_mul, map_pow, map_natCast]`. Establish `hb' : T.eB ((l : P.R.B) ^ (N + M) * ω') = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ N * x')`. Establish `e : (l : P.R.B) ^ (N + M) * ω' = (l : P.R.B) ^ N * ((l : P.R.B) ^ M * ω')` using `by ring`. Rewrite using `[e, map_mul T.eB ((l : P.R.B) ^ N), hx']`.

Simplify using `only [map_mul, map_pow, map_natCast]`. Establish `hu` using `isUnit_lpow (P := P) (N + M)`. Take `⟨c, hc⟩` from `ratio_integral T hs hb hb' (by rw [iter_lpow, he]; ring) (by rw [iter_lpow, he']; ring) (fun e => h0 ((hu.mul_right_eq_zero).1 e)) (by`. Simplify using `only [map_mul, map_pow, map_natCast]`. Take the linear combination `((l : P.R.B) ^ (N + M)) ^ 2 * hr)`.

Use `⟨c, hu.mul_left_cancel ?_⟩` and prove the remaining obligations. Rewrite using `[hc, Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratio_of_acris : Ratio := by
  intro l _ P AI T h s hs ω ω' hω hω' he he' h0 hr
  obtain ⟨N, x, hx⟩ := hω
  obtain ⟨M, x', hx'⟩ := hω'
  have hb : T.eB ((l : P.R.B) ^ (N + M) * ω) =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ M * x) := by
    have e : (l : P.R.B) ^ (N + M) * ω = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * ω) := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ M), hx]
    simp only [map_mul, map_pow, map_natCast]
  have hb' : T.eB ((l : P.R.B) ^ (N + M) * ω') =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ N * x') := by
    have e : (l : P.R.B) ^ (N + M) * ω' = (l : P.R.B) ^ N * ((l : P.R.B) ^ M * ω') := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ N), hx']
    simp only [map_mul, map_pow, map_natCast]
  have hu := isUnit_lpow (P := P) (N + M)
  obtain ⟨c, hc⟩ := ratio_integral T hs hb hb'
    (by rw [iter_lpow, he]; ring) (by rw [iter_lpow, he']; ring)
    (fun e => h0 ((hu.mul_right_eq_zero).1 e))
    (by
      simp only [map_mul, map_pow, map_natCast]
      linear_combination ((l : P.R.B) ^ (N + M)) ^ 2 * hr)
  refine ⟨c, hu.mul_left_cancel ?_⟩
  rw [hc, Algebra.smul_def, Algebra.smul_def]
  ring

end GlobalTheory.PMon.RatioTransport
