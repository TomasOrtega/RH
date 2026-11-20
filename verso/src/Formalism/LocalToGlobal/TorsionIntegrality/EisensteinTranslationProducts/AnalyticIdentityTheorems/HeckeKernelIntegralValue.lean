import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HkRowIntegral

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Filter Topology

namespace Formalism.L2.Th1.F
namespace Hk1

/- English proof (translation)
Rewrite using `[Real.rpow_neg hu.le, Real.rpow_two]`.
-/
lemma rpow_neg_two' {u : ℝ} (hu : 0 < u) : u ^ (-2 : ℝ) = (u ^ 2)⁻¹ := by
  rw [Real.rpow_neg hu.le, Real.rpow_two]

/- English proof (translation)
Establish `h0 : 0 < ‖w‖` using `norm_pos_iff.mpr hw`. Unfold `hk`. Rewrite using `[norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h0.le _)]`. Rewrite using `[show -(2 + 2 * s) = (-2 : ℝ) + -(2 * s) by ring, Real.rpow_add h0, rpow_neg_two' h0]`.
-/
lemma norm_hk (s : ℝ) (w : ℂ) (hw : w ≠ 0) : ‖hk s w‖ = ‖w‖ ^ (-(2 + 2 * s)) := by
  have h0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  unfold hk
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg h0.le _)]
  rw [show -(2 + 2 * s) = (-2 : ℝ) + -(2 * s) by ring, Real.rpow_add h0, rpow_neg_two' h0]

/- English proof (translation)
Distinguish the cases in `hw : w = 0`. Substitute `hw` using the available equality. Simplify using `only [hk]`. Simplify using the standard rewrite rules. Conclude with `Real.rpow_nonneg le_rfl _`.

Conclude with `(norm_hk s w hw).le`.
-/
lemma norm_hk_le (s : ℝ) (w : ℂ) : ‖hk s w‖ ≤ ‖w‖ ^ (-(2 + 2 * s)) := by
  by_cases hw : w = 0
  · subst hw
    simp only [hk]
    simp
    exact Real.rpow_nonneg le_rfl _
  · exact (norm_hk s w hw).le

/- English proof (translation)
Establish `h1` using `(EisensteinSeries.summable_one_div_norm_rpow (k := 2 + 2 * s) (by linarith)).mul_left ((EisensteinSeries.r z) ^ (-(2 + 2 * s)))`. Establish `h2 : Summable (fun x : Fin 2 → ℤ => ‖(x 0 : ℂ) * (z : ℂ) + x 1‖ ^ (-(2 + 2 * s)))` using `Summable.of_nonneg_of_le (fun x => Real.rpow_nonneg (norm_nonneg _) _) (fun x => EisensteinSeries.summand_bound z (by linarith) x) h1`. Establish `h3` using `(((Equiv.prodComm ℤ ℤ).trans (finTwoArrowEquiv ℤ).symm).summable_iff).mpr h2`. Use `h3.congr (fun p => ?_)` and prove the remaining obligations. Simplify using `[add_comm]`.
-/
lemma summable_upper (z : UpperHalfPlane) (s : ℝ) (hs : 0 < s) :
    Summable (fun p : ℤ × ℤ => ‖(p.1 : ℂ) + (p.2 : ℂ) * (z : ℂ)‖ ^ (-(2 + 2 * s))) := by
  have h1 := (EisensteinSeries.summable_one_div_norm_rpow (k := 2 + 2 * s) (by linarith)).mul_left
    ((EisensteinSeries.r z) ^ (-(2 + 2 * s)))
  have h2 : Summable (fun x : Fin 2 → ℤ => ‖(x 0 : ℂ) * (z : ℂ) + x 1‖ ^ (-(2 + 2 * s))) :=
    Summable.of_nonneg_of_le (fun x => Real.rpow_nonneg (norm_nonneg _) _)
      (fun x => EisensteinSeries.summand_bound z (by linarith) x) h1
  have h3 := (((Equiv.prodComm ℤ ℤ).trans (finTwoArrowEquiv ℤ).symm).summable_iff).mpr h2
  refine h3.congr (fun p => ?_)
  simp [add_comm]

/- English proof (translation)
Break down `lt_or_gt_of_ne hτ with h | h` into its components or cases. Establish `h' : 0 < (conj τ).im` using `by simpa using h`. Use `(summable_upper ⟨conj τ, h'⟩ s hs).congr (fun p => ?_)` and prove the remaining obligations. Establish `: (p.1 : ℂ) + (p.2 : ℂ) * conj τ = conj ((p.1 : ℂ) + (p.2 : ℂ) * τ)` using `by simp`. Use `show ‖(p.1 : ℂ) + (p.2 : ℂ) * conj τ‖ ^ _ = _`.

Rewrite using `[this, Complex.norm_conj]`. Conclude with `summable_upper ⟨τ, h⟩ s hs`.
-/
lemma summable_norm (τ : ℂ) (s : ℝ) (hτ : τ.im ≠ 0) (hs : 0 < s) :
    Summable (fun p : ℤ × ℤ => ‖(p.1 : ℂ) + (p.2 : ℂ) * τ‖ ^ (-(2 + 2 * s))) := by
  rcases lt_or_gt_of_ne hτ with h | h
  · have h' : 0 < (conj τ).im := by simpa using h
    refine (summable_upper ⟨conj τ, h'⟩ s hs).congr (fun p => ?_)
    have : (p.1 : ℂ) + (p.2 : ℂ) * conj τ = conj ((p.1 : ℂ) + (p.2 : ℂ) * τ) := by simp
    show ‖(p.1 : ℂ) + (p.2 : ℂ) * conj τ‖ ^ _ = _
    rw [this, Complex.norm_conj]
  · exact summable_upper ⟨τ, h⟩ s hs

/- English proof (translation)
Unfold `hk`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg _), show -(2 + 2 * s) = (-2 : ℝ) + -(2 * s) by ring, Real.rpow_add ha, rpow_neg_two' ha]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hk_smul (s a : ℝ) (ha : 0 < a) (w : ℂ) :
    hk s ((a : ℂ) * w) = ((a ^ (-(2 + 2 * s)) : ℝ) : ℂ) * hk s w := by
  unfold hk
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le,
    Real.mul_rpow ha.le (norm_nonneg _),
    show -(2 + 2 * s) = (-2 : ℝ) + -(2 * s) by ring, Real.rpow_add ha, rpow_neg_two' ha]
  push_cast
  ring

/- English proof (translation)
Establish `hu : 0 < 1 + t ^ 2` using `by positivity`. Establish `hn : ‖(t : ℂ) + (ε : ℂ) * Complex.I‖ = Real.sqrt (1 + t ^ 2)`. Rewrite using `[Complex.norm_add_mul_I, hε, add_comm]`. Establish `hεC : (ε : ℂ) ^ 2 = 1` using `by exact_mod_cast hε`. Establish `key : ((t : ℂ) + (ε : ℂ) * Complex.I) * ((t : ℂ) - (ε : ℂ) * Complex.I) = ((1 + t ^ 2 : ℝ) : ℂ)`.

Use `push_cast`. Take the linear combination `(-(ε : ℂ) ^ 2) * Complex.I_sq + hεC`. Establish `huC : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hu.ne'`. Establish `hw : (t : ℂ) + (ε : ℂ) * Complex.I ≠ 0`. Introduce `h`.

Rewrite `key` using `[h, zero_mul]`. Conclude with `huC key.symm`. Establish `hinv : (((t : ℂ) + (ε : ℂ) * Complex.I) ^ 2)⁻¹ = ((t : ℂ) - (ε : ℂ) * Complex.I) ^ 2 * ((((1 + t ^ 2 : ℝ) : ℂ)) ^ 2)⁻¹`. Rewrite using `[← key]`. Establish `h2 : (t : ℂ) - (ε : ℂ) * Complex.I ≠ 0`.

Introduce `h`. Rewrite `key` using `[h, mul_zero]`. Conclude with `huC key.symm`. Clear the denominators using the available nonvanishing facts. Unfold `hk`.

Rewrite using `[hn, hinv, Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le, show (1 / 2 : ℝ) * -(2 * s) = -s by ring, show -(1 + s) = (-1 : ℝ) + -s by ring, show -(2 + s) = (-2 : ℝ) + -s by ring, Real.rpow_add hu, Real.rpow_add hu, rpow_neg_two' hu, Real.rpow_neg_one]`. Use `set v : ℝ := (1 + t ^ 2) ^ (-s) with hv`. Establish `h1 : (((1 + t ^ 2 : ℝ))⁻¹ : ℝ) = (1 + t ^ 2) * ((1 + t ^ 2) ^ 2)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1]`.

Use `push_cast`. Take the linear combination `((((1 : ℂ) + (t : ℂ) ^ 2) ^ 2)⁻¹ * (v : ℂ)) * ((ε : ℂ) ^ 2 * Complex.I_sq - hεC)`.
-/
lemma hk_unit (s t ε : ℝ) (hε : ε ^ 2 = 1) :
    hk s ((t : ℂ) + (ε : ℂ) * Complex.I) =
      (((1 + t ^ 2) ^ (-(1 + s)) - 2 * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ)
        - 2 * ε * Complex.I * ((t * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ) := by
  have hu : 0 < 1 + t ^ 2 := by positivity
  have hn : ‖(t : ℂ) + (ε : ℂ) * Complex.I‖ = Real.sqrt (1 + t ^ 2) := by
    rw [Complex.norm_add_mul_I, hε, add_comm]
  have hεC : (ε : ℂ) ^ 2 = 1 := by exact_mod_cast hε
  have key : ((t : ℂ) + (ε : ℂ) * Complex.I) * ((t : ℂ) - (ε : ℂ) * Complex.I)
      = ((1 + t ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(ε : ℂ) ^ 2) * Complex.I_sq + hεC
  have huC : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hw : (t : ℂ) + (ε : ℂ) * Complex.I ≠ 0 := by
    intro h; rw [h, zero_mul] at key; exact huC key.symm
  have hinv : (((t : ℂ) + (ε : ℂ) * Complex.I) ^ 2)⁻¹
      = ((t : ℂ) - (ε : ℂ) * Complex.I) ^ 2 * ((((1 + t ^ 2 : ℝ) : ℂ)) ^ 2)⁻¹ := by
    rw [← key]
    have h2 : (t : ℂ) - (ε : ℂ) * Complex.I ≠ 0 := by
      intro h; rw [h, mul_zero] at key; exact huC key.symm
    field_simp
  unfold hk
  rw [hn, hinv, Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le,
    show (1 / 2 : ℝ) * -(2 * s) = -s by ring,
    show -(1 + s) = (-1 : ℝ) + -s by ring, show -(2 + s) = (-2 : ℝ) + -s by ring,
    Real.rpow_add hu, Real.rpow_add hu, rpow_neg_two' hu, Real.rpow_neg_one]
  set v : ℝ := (1 + t ^ 2) ^ (-s) with hv
  have h1 : (((1 + t ^ 2 : ℝ))⁻¹ : ℝ) = (1 + t ^ 2) * ((1 + t ^ 2) ^ 2)⁻¹ := by
    field_simp
  rw [h1]
  push_cast
  linear_combination ((((1 : ℂ) + (t : ℂ) ^ 2) ^ 2)⁻¹ * (v : ℂ)) * ((ε : ℂ) ^ 2 * Complex.I_sq - hεC)

/- English proof (translation)
Establish `h` using `integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * a) (by simp; linarith)`. Use `h.congr (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [Real.norm_eq_abs, sq_abs]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma integrable_J (a : ℝ) (ha : 1 / 2 < a) : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-a)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * a)
    (by simp; linarith)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

/- English proof (translation)
Use `(integrable_J (1 + s) (by linarith)).mono' (Measurable.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Establish `hu : 0 < 1 + t ^ 2` using `by positivity`. Establish `h1 : (1 + t ^ 2) ^ (-(1 + s)) = (1 + t ^ 2) * (1 + t ^ 2) ^ (-(2 + s))`. Rewrite using `[show -(1 + s) = (1 : ℝ) + -(2 + s) by ring, Real.rpow_add hu, Real.rpow_one]`. Rewrite using `[h1, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hu.le _)]`.

Use `mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu.le _)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> nlinarith [sq_nonneg (t + 1), sq_nonneg (t - 1)]`.
-/
lemma integrable_odd (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun t : ℝ => t * (1 + t ^ 2) ^ (-(2 + s))) := by
  refine (integrable_J (1 + s) (by linarith)).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun t => ?_)
  have hu : 0 < 1 + t ^ 2 := by positivity
  have h1 : (1 + t ^ 2) ^ (-(1 + s)) = (1 + t ^ 2) * (1 + t ^ 2) ^ (-(2 + s)) := by
    rw [show -(1 + s) = (1 : ℝ) + -(2 + s) by ring, Real.rpow_add hu, Real.rpow_one]
  rw [h1, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hu.le _)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu.le _)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg (t + 1), sq_nonneg (t - 1)]

/- English proof (translation)
Establish `h` using `integral_neg_eq_self (fun t : ℝ => t * (1 + t ^ 2) ^ (-(2 + s))) volume`. Simplify using `only [neg_sq, neg_mul, integral_neg] at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma integral_odd (s : ℝ) : ∫ t : ℝ, t * (1 + t ^ 2) ^ (-(2 + s)) = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => t * (1 + t ^ 2) ^ (-(2 + s))) volume
  simp only [neg_sq, neg_mul, integral_neg] at h
  linarith

/- English proof (translation)
Establish `e : (fun t : ℝ => hk s ((t : ℂ) + (ε : ℂ) * Complex.I)) = fun t : ℝ => (((1 + t ^ 2) ^ (-(1 + s)) - 2 * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ) - 2 * ε * Complex.I * ((t * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ)`. Use function extensionality and compare the values at `fun t => hk_unit s t ε hε`. Establish `i1` using `integrable_J (1 + s) (by linarith)`. Establish `i2` using `(integrable_J (2 + s) (by linarith)).const_mul 2`. Establish `iR : Integrable (fun t : ℝ => (((1 + t ^ 2) ^ (-(1 + s)) - 2 * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ))` using `(i1.sub i2).ofReal (𝕜 := ℂ)`.

Establish `iO : Integrable (fun t : ℝ => 2 * (ε : ℂ) * Complex.I * ((t * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ))` using `((integrable_odd s hs).ofReal (𝕜 := ℂ)).const_mul (2 * ε * Complex.I)`. Rewrite using `[e]`. Use `⟨iR.sub iO, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_sub iR iO, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal, integral_odd, integral_sub i1 i2, integral_const_mul]`. Simplify using `[hkJ]`.
-/
lemma unit_row (s ε : ℝ) (hs : 0 ≤ s) (hε : ε ^ 2 = 1) :
    Integrable (fun t : ℝ => hk s ((t : ℂ) + (ε : ℂ) * Complex.I)) ∧
    ∫ t : ℝ, hk s ((t : ℂ) + (ε : ℂ) * Complex.I) = ((hkJ (1 + s) - 2 * hkJ (2 + s) : ℝ) : ℂ) := by
  have e : (fun t : ℝ => hk s ((t : ℂ) + (ε : ℂ) * Complex.I)) = fun t : ℝ =>
      (((1 + t ^ 2) ^ (-(1 + s)) - 2 * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ)
        - 2 * ε * Complex.I * ((t * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ) :=
    funext fun t => hk_unit s t ε hε
  have i1 := integrable_J (1 + s) (by linarith)
  have i2 := (integrable_J (2 + s) (by linarith)).const_mul 2
  have iR : Integrable (fun t : ℝ =>
      (((1 + t ^ 2) ^ (-(1 + s)) - 2 * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ)) :=
    (i1.sub i2).ofReal (𝕜 := ℂ)
  have iO : Integrable (fun t : ℝ =>
      2 * (ε : ℂ) * Complex.I * ((t * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ)) :=
    ((integrable_odd s hs).ofReal (𝕜 := ℂ)).const_mul (2 * ε * Complex.I)
  rw [e]
  refine ⟨iR.sub iO, ?_⟩
  rw [integral_sub iR iO, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal, integral_odd,
    integral_sub i1 i2, integral_const_mul]
  simp [hkJ]

/- English proof (translation)
Establish `hc' : 0 < |c|` using `abs_pos.mpr hc`. Establish `hε : (c / |c|) ^ 2 = 1`. Rewrite using `[div_pow, sq_abs]`. Conclude with `div_self (pow_ne_zero 2 hc)`. Take `⟨iG, vG⟩` from `unit_row s (c / |c|) hs hε`.

Establish `e : (fun t : ℝ => hk s (((|c| * t : ℝ) : ℂ) + (c : ℂ) * Complex.I)) = fun t : ℝ => ((|c| ^ (-(2 + 2 * s)) : ℝ) : ℂ) * hk s ((t : ℂ) + ((c / |c| : ℝ) : ℂ) * Complex.I)`. Use function extensionality and compare the values at `t`. Rewrite using `[← hk_smul s |c| hc']`. Use `congr 1`. Establish `: ((|c| : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hc'.ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `i1 : Integrable (fun t : ℝ => hk s (((|c| * t : ℝ) : ℂ) + (c : ℂ) * Complex.I))`. Rewrite using `[e]`. Conclude with `iG.const_mul _`.

Establish `iH` using `(integrable_comp_mul_left_iff (fun x : ℝ => hk s ((x : ℂ) + (c : ℂ) * Complex.I)) hc'.ne').mp i1`. Use `⟨iH, ?_⟩` and prove the remaining obligations. Establish `h2` using `Measure.integral_comp_mul_left (fun x : ℝ => hk s ((x : ℂ) + (c : ℂ) * Complex.I)) |c|`. Rewrite `h2` using `[e, integral_const_mul, vG, abs_inv, abs_abs]`. Establish `h3 : ∫ x : ℝ, hk s ((x : ℂ) + (c : ℂ) * Complex.I) = |c| • (|c|⁻¹ • ∫ x : ℝ, hk s ((x : ℂ) + (c : ℂ) * Complex.I))`.

Rewrite using `[smul_smul, mul_inv_cancel₀ hc'.ne', one_smul]`. Rewrite using `[h3, ← h2, show -(1 + 2 * s) = (1 : ℝ) + -(2 + 2 * s) by ring, Real.rpow_add hc', Real.rpow_one, Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma vert_row (s c : ℝ) (hs : 0 ≤ s) (hc : c ≠ 0) :
    Integrable (fun x : ℝ => hk s ((x : ℂ) + (c : ℂ) * Complex.I)) ∧
    ∫ x : ℝ, hk s ((x : ℂ) + (c : ℂ) * Complex.I)
      = ((|c| ^ (-(1 + 2 * s)) * (hkJ (1 + s) - 2 * hkJ (2 + s)) : ℝ) : ℂ) := by
  have hc' : 0 < |c| := abs_pos.mpr hc
  have hε : (c / |c|) ^ 2 = 1 := by
    rw [div_pow, sq_abs]; exact div_self (pow_ne_zero 2 hc)
  obtain ⟨iG, vG⟩ := unit_row s (c / |c|) hs hε
  have e : (fun t : ℝ => hk s (((|c| * t : ℝ) : ℂ) + (c : ℂ) * Complex.I)) = fun t : ℝ =>
      ((|c| ^ (-(2 + 2 * s)) : ℝ) : ℂ) * hk s ((t : ℂ) + ((c / |c| : ℝ) : ℂ) * Complex.I) := by
    funext t
    rw [← hk_smul s |c| hc']
    congr 1
    have : ((|c| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
    push_cast
    field_simp
  have i1 : Integrable (fun t : ℝ => hk s (((|c| * t : ℝ) : ℂ) + (c : ℂ) * Complex.I)) := by
    rw [e]; exact iG.const_mul _
  have iH := (integrable_comp_mul_left_iff
    (fun x : ℝ => hk s ((x : ℂ) + (c : ℂ) * Complex.I)) hc'.ne').mp i1
  refine ⟨iH, ?_⟩
  have h2 := Measure.integral_comp_mul_left
    (fun x : ℝ => hk s ((x : ℂ) + (c : ℂ) * Complex.I)) |c|
  rw [e, integral_const_mul, vG, abs_inv, abs_abs] at h2
  have h3 : ∫ x : ℝ, hk s ((x : ℂ) + (c : ℂ) * Complex.I)
      = |c| • (|c|⁻¹ • ∫ x : ℝ, hk s ((x : ℂ) + (c : ℂ) * Complex.I)) := by
    rw [smul_smul, mul_inv_cancel₀ hc'.ne', one_smul]
  rw [h3, ← h2, show -(1 + 2 * s) = (1 : ℝ) + -(2 + 2 * s) by ring, Real.rpow_add hc',
    Real.rpow_one, Complex.real_smul]
  push_cast
  ring

/- English proof (translation)
Establish `hc : (n : ℝ) * τ.im ≠ 0` using `mul_ne_zero (by exact_mod_cast hn) hτ`. Take `⟨iH, vH⟩` from `vert_row s ((n : ℝ) * τ.im) hs hc`. Establish `e : (fun x : ℝ => hk s ((x : ℂ) + (n : ℂ) * τ)) = fun x : ℝ => (fun y : ℝ => hk s ((y : ℂ) + (((n : ℝ) * τ.im : ℝ) : ℂ) * Complex.I)) (x + (n : ℝ) * τ.re)`. Use function extensionality and compare the values at `x`. Simplify using `only`.

Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp`. Prove the components needed by the constructor for the conclusion. Rewrite using `[e]`. Conclude with `iH.comp_add_right _`.

Unfold `hkInt`. Rewrite using `[e, integral_add_right_eq_self (fun y : ℝ => hk s ((y : ℂ) + (((n : ℝ) * τ.im : ℝ) : ℂ) * Complex.I)), vH, abs_mul]`.
-/
lemma row (τ : ℂ) (s : ℝ) (n : ℤ) (hτ : τ.im ≠ 0) (hs : 0 ≤ s) (hn : n ≠ 0) :
    Integrable (fun x : ℝ => hk s ((x : ℂ) + (n : ℂ) * τ)) ∧
    hkInt τ s n = (((|(n : ℝ)| * |τ.im|) ^ (-(1 + 2 * s))
      * (hkJ (1 + s) - 2 * hkJ (2 + s)) : ℝ) : ℂ) := by
  have hc : (n : ℝ) * τ.im ≠ 0 := mul_ne_zero (by exact_mod_cast hn) hτ
  obtain ⟨iH, vH⟩ := vert_row s ((n : ℝ) * τ.im) hs hc
  have e : (fun x : ℝ => hk s ((x : ℂ) + (n : ℂ) * τ)) = fun x : ℝ =>
      (fun y : ℝ => hk s ((y : ℂ) + (((n : ℝ) * τ.im : ℝ) : ℂ) * Complex.I))
        (x + (n : ℝ) * τ.re) := by
    funext x
    simp only
    congr 1
    apply Complex.ext <;> simp
  constructor
  · rw [e]; exact iH.comp_add_right _
  · unfold hkInt
    rw [e, integral_add_right_eq_self
      (fun y : ℝ => hk s ((y : ℂ) + (((n : ℝ) * τ.im : ℝ) : ℂ) * Complex.I)), vH, abs_mul]

/- English proof (translation)
Establish `h1 : Tendsto (fun x : ℝ => ‖(x : ℂ) + c‖) l atTop`. Use `tendsto_atTop_mono (fun x => ?_) hl` and prove the remaining obligations. Simplify using `using Complex.abs_re_le_norm ((x : ℂ) + c)`. Establish `h2` using `tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp h1)`. Simplify using `using h2.neg`.
-/
lemma tendsto_neg_inv (c : ℂ) (l : Filter ℝ) (hl : Tendsto (fun x : ℝ => |x + c.re|) l atTop) :
    Tendsto (fun x : ℝ => -((x : ℂ) + c)⁻¹) l (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => ‖(x : ℂ) + c‖) l atTop := by
    refine tendsto_atTop_mono (fun x => ?_) hl
    simpa using Complex.abs_re_le_norm ((x : ℂ) + c)
  have h2 := tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp h1)
  simpa using h2.neg

end Hk1

/- English proof (translation)
Introduce `τ s hτ hs`. Conclude with `Summable.of_norm_bounded (Hk1.summable_norm τ s hτ hs) (fun p => Hk1.norm_hk_le s _)`.
-/
theorem hecke_kernel_summable : HkSummable := by
  intro τ s hτ hs
  exact Summable.of_norm_bounded (Hk1.summable_norm τ s hτ hs) (fun p => Hk1.norm_hk_le s _)

/- English proof (translation)
Introduce `τ s n hτ hs hn`. Establish `hI` using `(Hk1.row τ s n hτ hs hn).1`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Establish `h` using `hI.hasSum_intervalIntegral_comp_add_int`. Unfold `hkInt`.

Establish `e : (fun m : ℤ => ∫ x in (0 : ℝ)..1, hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)) = fun m : ℤ => ∫ x in (0 : ℝ)..1, hk s (((x + m : ℝ) : ℂ) + (n : ℂ) * τ)`. Use function extensionality and compare the values at `m`. Use `congr 1`. Use function extensionality and compare the values at `x`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h`.
-/
theorem hecke_kernel_line_integral : HkRowIntegral := by
  intro τ s n hτ hs hn
  have hI := (Hk1.row τ s n hτ hs hn).1
  refine ⟨hI, ?_⟩
  have h := hI.hasSum_intervalIntegral_comp_add_int
  unfold hkInt
  have e : (fun m : ℤ => ∫ x in (0 : ℝ)..1, hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ))
      = fun m : ℤ => ∫ x in (0 : ℝ)..1, hk s (((x + m : ℝ) : ℂ) + (n : ℂ) * τ) := by
    funext m
    congr 1
    funext x
    congr 1
    push_cast
    ring
  rw [e]
  exact h

/- English proof (translation)
Introduce `τ s n hτ hs hn`. Conclude with `(Hk1.row τ s n hτ hs.le hn).2`.
-/
theorem hecke_kernel_integral_value : HkIntValue := by
  intro τ s n hτ hs hn
  exact (Hk1.row τ s n hτ hs.le hn).2

/- English proof (translation)
Introduce `τ n hτ hn`. Establish `hI` using `(Hk1.row τ 0 n hτ le_rfl hn).1`. Establish `hne : ∀ x : ℝ, (x : ℂ) + (n : ℂ) * τ ≠ 0`. Introduce `x h`. Establish `h'` using `congrArg Complex.im h`.

Simplify using `at h'`. Break down `h' with h' | h'` into its components or cases. Conclude with `hn h'`. Conclude with `hτ h'`. Establish `e : (fun x : ℝ => hk 0 ((x : ℂ) + (n : ℂ) * τ)) = fun x : ℝ => (((x : ℂ) + (n : ℂ) * τ) ^ 2)⁻¹`.

Use function extensionality and compare the values at `x`. Simplify using `[hk]`. Establish `hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -((x : ℂ) + (n : ℂ) * τ)⁻¹) ((((x : ℂ) + (n : ℂ) * τ) ^ 2)⁻¹) x`. Introduce `x`. Establish `h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + (n : ℂ) * τ) 1 x` using `(Complex.ofRealCLM.hasDerivAt (x := x)).add_const _`.

Establish `h2` using `(h1.inv (hne x)).neg`. Establish `h3 : (((x : ℂ) + (n : ℂ) * τ) ^ 2)⁻¹ = -(-1 / ((x : ℂ) + (n : ℂ) * τ) ^ 2)`. Rewrite using `[neg_div, neg_neg, one_div]`. Rewrite using `[h3]`. Conclude with `h2`.

Rewrite `hI` using `[e]`. Unfold `hkInt`. Rewrite using `[e, integral_of_hasDerivAt_of_tendsto hd hI (Hk1.tendsto_neg_inv _ _ (tendsto_abs_atBot_atTop.comp (tendsto_atBot_add_const_right _ _ tendsto_id))) (Hk1.tendsto_neg_inv _ _ (tendsto_abs_atTop_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_id)))]`. Simplify using the standard rewrite rules.
-/
theorem hecke_kernel_integral_zero : HkIntZero := by
  intro τ n hτ hn
  have hI := (Hk1.row τ 0 n hτ le_rfl hn).1
  have hne : ∀ x : ℝ, (x : ℂ) + (n : ℂ) * τ ≠ 0 := by
    intro x h
    have h' := congrArg Complex.im h
    simp at h'
    rcases h' with h' | h'
    · exact hn h'
    · exact hτ h'
  have e : (fun x : ℝ => hk 0 ((x : ℂ) + (n : ℂ) * τ))
      = fun x : ℝ => (((x : ℂ) + (n : ℂ) * τ) ^ 2)⁻¹ := by
    funext x; simp [hk]
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -((x : ℂ) + (n : ℂ) * τ)⁻¹)
      ((((x : ℂ) + (n : ℂ) * τ) ^ 2)⁻¹) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + (n : ℂ) * τ) 1 x :=
      (Complex.ofRealCLM.hasDerivAt (x := x)).add_const _
    have h2 := (h1.inv (hne x)).neg
    have h3 : (((x : ℂ) + (n : ℂ) * τ) ^ 2)⁻¹ = -(-1 / ((x : ℂ) + (n : ℂ) * τ) ^ 2) := by
      rw [neg_div, neg_neg, one_div]
    rw [h3]
    exact h2
  rw [e] at hI
  unfold hkInt
  rw [e, integral_of_hasDerivAt_of_tendsto hd hI
    (Hk1.tendsto_neg_inv _ _ (tendsto_abs_atBot_atTop.comp
      (tendsto_atBot_add_const_right _ _ tendsto_id)))
    (Hk1.tendsto_neg_inv _ _ (tendsto_abs_atTop_atTop.comp
      (tendsto_atTop_add_const_right _ _ tendsto_id)))]
  simp

end Formalism.L2.Th1.F
