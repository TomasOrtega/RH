import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

/- English proof (translation)
Use `set x := z.1.re with hx`. Use `set y := z.1.im with hy`. Establish `hden : den m z.1 ≠ 0` using `den_ne m z.2`. Establish `hnd : 0 < Complex.normSq (den m z.1)` using `Complex.normSq_pos.2 hden`. Establish `hdet : m.val.det = a ^ 2 + b ^ 2` using `by rw [det_eq, h00, h01, h10, h11]; ring`.

Establish `hb2 : 0 < b ^ 2` using `by positivity`. Establish `hs : 0 < a ^ 2 + b ^ 2` using `by positivity`. Establish `hwim : (m • z).1.im = (a ^ 2 + b ^ 2) * y / Complex.normSq (den m z.1)`. Rewrite using `[coe_smul, im_div, hdet]`. Establish `hwpos : 0 < (m • z).1.im` using `by rw [hwim]; positivity`.

Establish `hconj : z.1 - conj (m • z).1 = (z.1 * conj (den m z.1) - conj (num m z.1)) / conj (den m z.1)`. Establish `: conj (den m z.1) ≠ 0` using `(map_ne_zero _).2 hden`. Rewrite using `[coe_smul, map_div₀]`. Clear the denominators using the available nonvanishing facts. Establish `hE : Complex.normSq (z.1 * conj (den m z.1) - conj (num m z.1)) = b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2`.

Rewrite using `[Complex.normSq_apply]`. Simplify using `[num, den, h00, h01, h10, h11, ← hx, ← hy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hN : ‖z.1 - conj (m • z).1‖ ^ 2 = (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) / Complex.normSq (den m z.1)`. Rewrite using `[hconj, Complex.sq_norm, Complex.normSq_div, Complex.normSq_conj, hE]`.

Establish `hI : ‖iP.1 - conj z.1‖ ^ 2 = x ^ 2 + (1 + y) ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[iP, ← hx, ← hy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hk1 : kap z (m • z) = 4 * (a ^ 2 + b ^ 2) * y ^ 2 / (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2)`.

Rewrite using `[kap, if_pos (mul_pos hz hwpos), hN, hwim]`. Simplify using `only [← hy]`. Clear the denominators using the available nonvanishing facts. Establish `hk2 : kap iP z = 4 * y / (x ^ 2 + (1 + y) ^ 2)`. Rewrite using `[kap, if_pos (by simpa [iP] using hz), hI]`.

Simplify using `[iP, ← hy]`. Rewrite using `[hk1, hk2]`. Establish `hQ : 0 < b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2` using `by positivity`. Establish `hR : 0 < x ^ 2 + (1 + y) ^ 2` using `by positivity`. Rewrite using `[div_mul_div_comm, div_le_div_iff₀ hQ (mul_pos hb2 hR)]`.

Establish `h1 : 2 * y ≤ x ^ 2 + y ^ 2 + 1` using `by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]`. Establish `key : b ^ 2 * (y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2) ≤ b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2`. Establish `: y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2 ≤ (x ^ 2 + y ^ 2 + 1) ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left this hb2.le, sq_nonneg a, sq_nonneg y]`. Establish `e : x ^ 2 + (1 + y) ^ 2 = (x ^ 2 + y ^ 2 + 1) + 2 * y` using `by ring`.

Rewrite using `[e]`. Establish `hs' : 0 ≤ 4 * (a ^ 2 + b ^ 2) * y` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left key hs']`.
-/
theorem kap_rot (m : GL (Fin 2) ℝ) (a b : ℝ) (h00 : m 0 0 = a) (h01 : m 0 1 = b)
    (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) (z : P) (hz : 0 < z.1.im) :
    kap z (m • z) ≤ (a ^ 2 + b ^ 2) / b ^ 2 * kap iP z := by
  set x := z.1.re with hx
  set y := z.1.im with hy
  have hden : den m z.1 ≠ 0 := den_ne m z.2
  have hnd : 0 < Complex.normSq (den m z.1) := Complex.normSq_pos.2 hden
  have hdet : m.val.det = a ^ 2 + b ^ 2 := by rw [det_eq, h00, h01, h10, h11]; ring
  have hb2 : 0 < b ^ 2 := by positivity
  have hs : 0 < a ^ 2 + b ^ 2 := by positivity
  have hwim : (m • z).1.im = (a ^ 2 + b ^ 2) * y / Complex.normSq (den m z.1) := by
    rw [coe_smul, im_div, hdet]
  have hwpos : 0 < (m • z).1.im := by rw [hwim]; positivity
  have hconj : z.1 - conj (m • z).1 = (z.1 * conj (den m z.1) - conj (num m z.1)) / conj (den m z.1) := by
    have : conj (den m z.1) ≠ 0 := (map_ne_zero _).2 hden
    rw [coe_smul, map_div₀]
    field_simp
  have hE : Complex.normSq (z.1 * conj (den m z.1) - conj (num m z.1)) =
      b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by
    rw [Complex.normSq_apply]
    simp [num, den, h00, h01, h10, h11, ← hx, ← hy]
    ring
  have hN : ‖z.1 - conj (m • z).1‖ ^ 2 = (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) / Complex.normSq (den m z.1) := by
    rw [hconj, Complex.sq_norm, Complex.normSq_div, Complex.normSq_conj, hE]
  have hI : ‖iP.1 - conj z.1‖ ^ 2 = x ^ 2 + (1 + y) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [iP, ← hx, ← hy]
    ring
  have hk1 : kap z (m • z) = 4 * (a ^ 2 + b ^ 2) * y ^ 2 / (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) := by
    rw [kap, if_pos (mul_pos hz hwpos), hN, hwim]
    simp only [← hy]
    field_simp
  have hk2 : kap iP z = 4 * y / (x ^ 2 + (1 + y) ^ 2) := by
    rw [kap, if_pos (by simpa [iP] using hz), hI]
    simp [iP, ← hy]
  rw [hk1, hk2]
  have hQ : 0 < b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by positivity
  have hR : 0 < x ^ 2 + (1 + y) ^ 2 := by positivity
  rw [div_mul_div_comm, div_le_div_iff₀ hQ (mul_pos hb2 hR)]
  have h1 : 2 * y ≤ x ^ 2 + y ^ 2 + 1 := by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
  have key : b ^ 2 * (y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2) ≤ b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by
    have : y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2 ≤ (x ^ 2 + y ^ 2 + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hb2.le, sq_nonneg a, sq_nonneg y]
  have e : x ^ 2 + (1 + y) ^ 2 = (x ^ 2 + y ^ 2 + 1) + 2 * y := by ring
  rw [e]
  have hs' : 0 ≤ 4 * (a ^ 2 + b ^ 2) * y := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hs']

/- English proof (translation)
Establish `htr : g.val.trace = g 0 0 + g 1 1` using `Matrix.trace_fin_two _`. Rewrite `hg` using `[htr, det_eq]`. Use `set p := g 0 0 with hp`. Use `set q := g 0 1 with hq`. Use `set r := g 1 0 with hr`.

Use `set t := g 1 1 with ht`. Use `set D := 4 * (p * t - q * r) - (p + t) ^ 2 with hD`. Establish `hD0 : 0 < D` using `by rw [hD]; linarith`. Establish `hr0 : r ≠ 0`. Introduce `h0`.

Rewrite `hg` using `[h0]`. Use polynomial arithmetic with `[sq_nonneg (p - t)]`. Use `set sD := Real.sqrt D with hsD`. Establish `hsD0 : 0 < sD` using `Real.sqrt_pos.2 hD0`. Establish `hsD2 : (sD : ℂ) ^ 2 = (D : ℂ)`.

Rewrite using `[← Complex.ofReal_pow, hsD, Real.sq_sqrt hD0.le]`. Use `set z0 : ℂ := (((p - t : ℝ) : ℂ) + Complex.I * sD) / (2 * (r : ℂ)) with hz0`. Establish `hrc : (r : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hr0`. Establish `him : z0.im ≠ 0`. Establish `: z0 = (((p - t) / (2 * r) : ℝ) : ℂ) + ((sD / (2 * r) : ℝ) : ℂ) * Complex.I`.

Rewrite using `[hz0]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Simplify using `only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]`.

Rewrite using `[add_zero]`. Conclude with `div_ne_zero hsD0.ne' (mul_ne_zero two_ne_zero hr0)`. Establish `hz : (2 * (r : ℂ)) * z0 = ((p - t : ℝ) : ℂ) + Complex.I * sD`. Rewrite using `[hz0]`. Clear the denominators using the available nonvanishing facts.

Establish `hquad : (r : ℂ) * z0 ^ 2 + ((t : ℂ) - p) * z0 - q = 0`. Establish `h4 : (4 * (r : ℂ)) ≠ 0` using `mul_ne_zero (by norm_num) hrc`. Apply `mul_left_cancel₀ h4` to reduce the goal to its premises. Rewrite using `[mul_zero]`. Establish `hDc : (D : ℂ) = 4 * ((p : ℂ) * t - q * r) - (p + t) ^ 2` using `by rw [hD]; push_cast; ring`.

Rewrite `hsD2` using `[hDc]`. Move the coercions through the operations in `at hz`. Take the linear combination `(2 * (r : ℂ) * z0 + ((p : ℂ) - t + Complex.I * sD) + 2 * ((t : ℂ) - p)) * hz + (sD : ℂ) ^ 2 * Complex.I_sq - hsD2`. Use `⟨(⟨z0, him⟩ : P), Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `num g z0 / den g z0 = z0`.

Establish `hd` using `den_ne g (z := z0) him`. Rewrite using `[div_eq_iff hd]`. Simplify using `only [num, den]`. Rewrite using `[← hp, ← hq, ← hr, ← ht]`. Take the linear combination `(-1 : ℂ) * hquad`.
-/
theorem exists_fix (g : GL (Fin 2) ℝ) (hg : g.val.trace ^ 2 < 4 * g.val.det) : ∃ z : P, g • z = z := by
  have htr : g.val.trace = g 0 0 + g 1 1 := Matrix.trace_fin_two _
  rw [htr, det_eq] at hg
  set p := g 0 0 with hp
  set q := g 0 1 with hq
  set r := g 1 0 with hr
  set t := g 1 1 with ht
  set D := 4 * (p * t - q * r) - (p + t) ^ 2 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0] at hg
    nlinarith [sq_nonneg (p - t)]
  set sD := Real.sqrt D with hsD
  have hsD0 : 0 < sD := Real.sqrt_pos.2 hD0
  have hsD2 : (sD : ℂ) ^ 2 = (D : ℂ) := by
    rw [← Complex.ofReal_pow, hsD, Real.sq_sqrt hD0.le]
  set z0 : ℂ := (((p - t : ℝ) : ℂ) + Complex.I * sD) / (2 * (r : ℂ)) with hz0
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0
  have him : z0.im ≠ 0 := by
    have : z0 = (((p - t) / (2 * r) : ℝ) : ℂ) + ((sD / (2 * r) : ℝ) : ℂ) * Complex.I := by
      rw [hz0]; push_cast; field_simp
    rw [this]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add]
    rw [add_zero]
    exact div_ne_zero hsD0.ne' (mul_ne_zero two_ne_zero hr0)
  have hz : (2 * (r : ℂ)) * z0 = ((p - t : ℝ) : ℂ) + Complex.I * sD := by
    rw [hz0]; field_simp
  have hquad : (r : ℂ) * z0 ^ 2 + ((t : ℂ) - p) * z0 - q = 0 := by
    have h4 : (4 * (r : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hrc
    apply mul_left_cancel₀ h4
    rw [mul_zero]
    have hDc : (D : ℂ) = 4 * ((p : ℂ) * t - q * r) - (p + t) ^ 2 := by rw [hD]; push_cast; ring
    rw [hDc] at hsD2
    push_cast at hz
    linear_combination (2 * (r : ℂ) * z0 + ((p : ℂ) - t + Complex.I * sD) + 2 * ((t : ℂ) - p)) * hz
      + (sD : ℂ) ^ 2 * Complex.I_sq - hsD2
  refine ⟨(⟨z0, him⟩ : P), Subtype.ext ?_⟩
  change num g z0 / den g z0 = z0
  have hd := den_ne g (z := z0) him
  rw [div_eq_iff hd]
  simp only [num, den]
  rw [← hp, ← hq, ← hr, ← ht]
  linear_combination (-1 : ℂ) * hquad

end UpperTheory.Esk.RadialIntegralLemmas
