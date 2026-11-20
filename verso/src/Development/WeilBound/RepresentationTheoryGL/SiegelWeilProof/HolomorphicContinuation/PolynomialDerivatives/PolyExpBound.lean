import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.HasFDerivAtEvX
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareNormBound

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def Sg (c : ℝ) : PX m n := C (-(c : ℂ)) * ∑ a, ∑ i, X (a, i, true) * X (a, i, false)

/- English proof (translation)
Unfold `gs`. Use `congr 1`. Simplify using `only [Sg, evX_eq, map_mul, map_sum, eval_C, eval_X, crd_apply, if_true, Bool.false_eq_true, if_false, Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gs_eq (c : ℝ) (x : Fin m → Fin n → ℂ) : gs c x = Complex.exp (evX (Sg c) x) := by
  unfold gs
  congr 1
  simp only [Sg, evX_eq, map_mul, map_sum, eval_C, eval_X, crd_apply, if_true, Bool.false_eq_true, if_false,
    Complex.star_def, Complex.conj_mul']
  push_cast
  ring

/- English proof (translation)
The claim follows from `continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt`.
-/
theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp [evX_eq]⟩`. Consider the case `add p q hp hq`. Take `⟨K1, d1, h1, b1⟩` from `hp`. Take `⟨K2, d2, h2, b2⟩` from `hq`.

Use `⟨K1 + K2, max d1 d2, by positivity, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : 1 ≤ 1 + ‖x‖` using `by linarith [norm_nonneg x]`. Establish `e1 : (1 + ‖x‖) ^ d1 ≤ (1 + ‖x‖) ^ max d1 d2` using `pow_le_pow_right₀ hx (le_max_left _ _)`. Establish `e2 : (1 + ‖x‖) ^ d2 ≤ (1 + ‖x‖) ^ max d1 d2` using `pow_le_pow_right₀ hx (le_max_right _ _)`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `mul_X p k hp`. Take `⟨K, d, hK, b⟩` from `hp`. Use `⟨K, d + 1, hK, fun x => ?_⟩` and prove the remaining obligations. Establish `hc : ‖crd k x‖ ≤ 1 + ‖x‖` using `(norm_crd_le k x).trans (by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem evX_bound (P : PX m n) : ∃ K : ℝ, ∃ d : ℕ, 0 ≤ K ∧ ∀ x, ‖evX P x‖ ≤ K * (1 + ‖x‖) ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨K1, d1, h1, b1⟩ := hp
    obtain ⟨K2, d2, h2, b2⟩ := hq
    refine ⟨K1 + K2, max d1 d2, by positivity, fun x => ?_⟩
    have hx : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have e1 : (1 + ‖x‖) ^ d1 ≤ (1 + ‖x‖) ^ max d1 d2 := pow_le_pow_right₀ hx (le_max_left _ _)
    have e2 : (1 + ‖x‖) ^ d2 ≤ (1 + ‖x‖) ^ max d1 d2 := pow_le_pow_right₀ hx (le_max_right _ _)
    calc ‖evX (p + q) x‖ ≤ ‖evX p x‖ + ‖evX q x‖ := by simpa [evX_eq] using norm_add_le _ _
      _ ≤ K1 * (1 + ‖x‖) ^ d1 + K2 * (1 + ‖x‖) ^ d2 := add_le_add (b1 x) (b2 x)
      _ ≤ K1 * (1 + ‖x‖) ^ max d1 d2 + K2 * (1 + ‖x‖) ^ max d1 d2 :=
        add_le_add (mul_le_mul_of_nonneg_left e1 h1) (mul_le_mul_of_nonneg_left e2 h2)
      _ = (K1 + K2) * (1 + ‖x‖) ^ max d1 d2 := by ring
  | mul_X p k hp =>
    obtain ⟨K, d, hK, b⟩ := hp
    refine ⟨K, d + 1, hK, fun x => ?_⟩
    have hc : ‖crd k x‖ ≤ 1 + ‖x‖ := (norm_crd_le k x).trans (by linarith)
    calc ‖evX (p * X k) x‖ = ‖evX p x‖ * ‖crd k x‖ := by simp [evX_eq]
      _ ≤ (K * (1 + ‖x‖) ^ d) * (1 + ‖x‖) := mul_le_mul (b x) hc (norm_nonneg _) (by positivity)
      _ = K * (1 + ‖x‖) ^ (d + 1) := by ring

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le x`.
-/
theorem sq_norm_le (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le x

/- English proof (translation)
Unfold `gs`. Rewrite using `[show (-(↑(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℂ)) = ↑(-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) by push_cast; ring, Complex.norm_exp_ofReal]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use `sq_norm_le x` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_gs_le (c : ℝ) (hc : 0 < c) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
  unfold gs
  rw [show (-(↑(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℂ)) = ↑(-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) by push_cast; ring,
    Complex.norm_exp_ofReal]
  apply Real.exp_le_exp.2
  have := sq_norm_le x
  nlinarith

/- English proof (translation)
Use `set y := 2 * c * (1 + t) with hy`. Establish `hy0 : 0 ≤ y` using `by positivity`. Establish `h1 : Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * Real.exp (-y)`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises.

Use polynomial arithmetic with `[sq_nonneg (t - 1)]`. Establish `h2 : (1 + t) ^ N * Real.exp (-y) ≤ (N.factorial : ℝ) / (2 * c) ^ N`. Use `Real.pow_div_factorial_le_exp y hy0 N` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ (by positivity)]`. Rewrite using `[le_div_iff₀ (by positivity)]`.

Establish `hyN : y ^ N = (2 * c) ^ N * (1 + t) ^ N` using `by rw [hy, mul_pow]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem poly_exp_bound (c : ℝ) (hc : 0 < c) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * ((N.factorial : ℝ) / (2 * c) ^ N) := by
  set y := 2 * c * (1 + t) with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * Real.exp (-y) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg (t - 1)]
  have h2 : (1 + t) ^ N * Real.exp (-y) ≤ (N.factorial : ℝ) / (2 * c) ^ N := by
    have := Real.pow_div_factorial_le_exp y hy0 N
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    have hyN : y ^ N = (2 * c) ^ N * (1 + t) ^ N := by rw [hy, mul_pow]
    calc (1 + t) ^ N * Real.exp (-y) * (2 * c) ^ N = y ^ N * Real.exp (-y) := by rw [hyN]; ring
      _ ≤ (Real.exp y * N.factorial) * Real.exp (-y) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = N.factorial := by rw [mul_comm (Real.exp y), mul_assoc, ← Real.exp_add]; simp
  calc (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ (1 + t) ^ N * (Real.exp (3 * c) * Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp (3 * c) * ((1 + t) ^ N * Real.exp (-y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

instance instHaarX : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
  MeasureTheory.Measure.pi.isAddHaarMeasure _

/- English proof (translation)
Repeatedly rewrite using `[gs_eq]`. Conclude with `Complex.continuous_exp.comp (continuous_evX _)`.
-/
theorem continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  simp_rw [gs_eq]; exact Complex.continuous_exp.comp (continuous_evX _)

/- English proof (translation)
Take `⟨K, d, hK, hb⟩` from `evX_bound P`. Use `set R : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hR`. Use `set M := Real.exp (3 * c) * (((d + R).factorial : ℝ) / (2 * c) ^ (d + R)) with hM`. Establish `hcont : Continuous (fun x : Fin m → Fin n → ℂ => evX P x * gs c x)` using `(continuous_evX P).mul (continuous_gs c)`. Use `((integrable_one_add_norm (E := Fin m → Fin n → ℂ) (μ := volume) (r := (R : ℝ)) (by simp [hR])).const_mul (K * M)).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Establish `ht : 0 ≤ ‖x‖` using `norm_nonneg x`. Establish `hpos : 0 < (1 + ‖x‖) ^ R` using `by positivity`. Establish `key` using `poly_exp_bound c hc (d + R) ‖x‖ ht`. Rewrite using `[norm_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[pow_add]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ K * M / (1 + ‖x‖) ^ R := by`. Apply `div_le_div_of_nonneg_right _ hpos.le` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left key hK`.

Use `_ = K * M * ((1 + ‖x‖) ^ R)⁻¹ := by rw [div_eq_mul_inv]`.
-/
theorem integrable_pg (c : ℝ) (hc : 0 < c) (P : PX m n) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := by
  obtain ⟨K, d, hK, hb⟩ := evX_bound P
  set R : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hR
  set M := Real.exp (3 * c) * (((d + R).factorial : ℝ) / (2 * c) ^ (d + R)) with hM
  have hcont : Continuous (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := (continuous_evX P).mul (continuous_gs c)
  refine ((integrable_one_add_norm (E := Fin m → Fin n → ℂ) (μ := volume) (r := (R : ℝ)) (by simp [hR])).const_mul
    (K * M)).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have ht : 0 ≤ ‖x‖ := norm_nonneg x
  have hpos : 0 < (1 + ‖x‖) ^ R := by positivity
  have key := poly_exp_bound c hc (d + R) ‖x‖ ht
  rw [norm_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (K * (1 + ‖x‖) ^ d) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul (hb x) (norm_gs_le c hc x) (norm_nonneg _) (by positivity)
    _ = K * ((1 + ‖x‖) ^ (d + R) * Real.exp (-(c * ‖x‖ ^ 2))) / (1 + ‖x‖) ^ R := by
        rw [pow_add]; field_simp
    _ ≤ K * M / (1 + ‖x‖) ^ R := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_left key hK
    _ = K * M * ((1 + ‖x‖) ^ R)⁻¹ := by rw [div_eq_mul_inv]

end PositivityTheory.Rg.Sw.LC.NullS
