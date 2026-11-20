import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff

noncomputable section

open MeasureTheory Matrix Set
open Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.GodementFE

/- English proof (translation)
Establish `h1 : (a : ℂ) ≠ 0` using `a.ne_zero`. Establish `h2 : ((‖(a : ℂ)‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (norm_ne_zero_iff.2 h1)`. Conclude with `div_ne_zero h1 h2`.
-/
theorem e_ne (a : ℂˣ) : ((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) ≠ 0 := by
  have h1 : (a : ℂ) ≠ 0 := a.ne_zero
  have h2 : ((‖(a : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h1)
  exact div_ne_zero h1 h2

/- English proof (translation)
Establish `h1 : (a : ℂ) ≠ 0` using `a.ne_zero`. Establish `h2 : ‖(a : ℂ)‖ ≠ 0` using `norm_ne_zero_iff.2 h1`. Conclude with `pow_ne_zero 2 h2` after adjusting the coercions.
-/
theorem r_ne (a : ℂˣ) : (((‖(a : ℂ)‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
  have h1 : (a : ℂ) ≠ 0 := a.ne_zero
  have h2 : ‖(a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 h1
  exact_mod_cast pow_ne_zero 2 h2

/- English proof (translation)
Unfold `ph`. Rewrite using `[← mul_zpow]`. Use `congr 1`. Rewrite using `[norm_mul]`. Use `push_cast`.

Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Distinguish the cases in `hb : b = 0`. Simplify using `[hb]`. Establish `h1 : ((‖a‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (norm_ne_zero_iff.2 ha)`.

Establish `h2 : ((‖b‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (norm_ne_zero_iff.2 hb)`. Clear the denominators using the available nonvanishing facts.
-/
theorem ph_mul (n : ℤ) (a b : ℂ) : ph n (a * b) = ph n a * ph n b := by
  unfold ph
  rw [← mul_zpow]
  congr 1
  rw [norm_mul]
  push_cast
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have h1 : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 ha)
  have h2 : ((‖b‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hb)
  field_simp

/- English proof (translation)
Unfold `chC`. Rewrite using `[zpow_add₀ (e_ne a), Complex.cpow_add _ _ (r_ne a)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chC_add (p q : ℤ) (s s' : ℂ) (a : ℂˣ) :
    chC p s a * chC q s' a = chC (p + q) (s + s') a := by
  unfold chC
  rw [zpow_add₀ (e_ne a), Complex.cpow_add _ _ (r_ne a)]
  ring

/- English proof (translation)
Unfold `chC`. Establish `h1 : ((a * b : ℂˣ) : ℂ) = (a : ℂ) * b` using `rfl`. Establish `h2 : ((a : ℂ) * b) / (‖(a : ℂ) * b‖ : ℂ) = ((a : ℂ) / ‖(a : ℂ)‖) * ((b : ℂ) / ‖(b : ℂ)‖)`. Use `e_ne a` as an intermediate fact. Use `e_ne b` as an intermediate fact.

Rewrite using `[norm_mul]`. Use `push_cast`. Rewrite using `[mul_div_mul_comm]`. Establish `h3 : (((‖(a : ℂ) * b‖ ^ 2 : ℝ)) : ℂ) ^ s = (((‖(a : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ s * (((‖(b : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ s`. Rewrite using `[norm_mul, mul_pow, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]`.

Rewrite using `[h1, h2, h3, mul_zpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chC_mul (p : ℤ) (s : ℂ) (a b : ℂˣ) : chC p s (a * b) = chC p s a * chC p s b := by
  unfold chC
  have h1 : ((a * b : ℂˣ) : ℂ) = (a : ℂ) * b := rfl
  have h2 : ((a : ℂ) * b) / (‖(a : ℂ) * b‖ : ℂ) = ((a : ℂ) / ‖(a : ℂ)‖) * ((b : ℂ) / ‖(b : ℂ)‖) := by
    have := e_ne a
    have := e_ne b
    rw [norm_mul]
    push_cast
    rw [mul_div_mul_comm]
  have h3 : (((‖(a : ℂ) * b‖ ^ 2 : ℝ)) : ℂ) ^ s =
      (((‖(a : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ s * (((‖(b : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ s := by
    rw [norm_mul, mul_pow, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  rw [h1, h2, h3, mul_zpow]
  ring

/- English proof (translation)
Simplify using `[chC]`.
-/
theorem chC_zero (a : ℂˣ) : chC 0 0 a = 1 := by
  simp [chC]

/- English proof (translation)
Simplify using `[chC]`.
-/
theorem chC_one (p : ℤ) (s : ℂ) : chC p s 1 = 1 := by
  simp [chC]

/- English proof (translation)
Unfold `chC`. Conclude with `mul_ne_zero (zpow_ne_zero _ (e_ne a)) (by simp [Complex.cpow_eq_zero_iff, r_ne a])`.
-/
theorem chC_ne (p : ℤ) (s : ℂ) (a : ℂˣ) : chC p s a ≠ 0 := by
  unfold chC
  exact mul_ne_zero (zpow_ne_zero _ (e_ne a)) (by simp [Complex.cpow_eq_zero_iff, r_ne a])

/- English proof (translation)
Establish `h1 : chC p s a⁻¹ * chC p s a = 1`. Rewrite using `[← chC_mul, inv_mul_cancel, chC_one]`. Establish `h2 : chC (-p) (-s) a * chC p s a = 1`. Rewrite using `[chC_add]`. Simplify using `[chC_zero]`.

Conclude with `mul_right_cancel₀ (chC_ne p s a) (h1.trans h2.symm)`.
-/
theorem chC_inv (p : ℤ) (s : ℂ) (a : ℂˣ) : chC p s a⁻¹ = chC (-p) (-s) a := by
  have h1 : chC p s a⁻¹ * chC p s a = 1 := by
    rw [← chC_mul, inv_mul_cancel, chC_one]
  have h2 : chC (-p) (-s) a * chC p s a = 1 := by
    rw [chC_add]
    simp [chC_zero]
  exact mul_right_cancel₀ (chC_ne p s a) (h1.trans h2.symm)

/- English proof (translation)
Unfold `chC ph`. Use `congr 1`. Establish `h0 : (0 : ℝ) ≤ ‖(a : ℂ)‖` using `norm_nonneg _`. Establish `e : (((‖(a : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = (((‖(a : ℂ)‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_cpow (by positivity)]`.

Evaluate the numerical expressions. Rewrite using `[e, ← Real.sqrt_eq_rpow, Real.sqrt_sq h0]`.
-/
theorem chC_half (p : ℤ) (a : ℂˣ) : chC p (1 / 2) a = ph p a * ((‖(a : ℂ)‖ : ℝ) : ℂ) := by
  unfold chC ph
  congr 1
  have h0 : (0 : ℝ) ≤ ‖(a : ℂ)‖ := norm_nonneg _
  have e : (((‖(a : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = (((‖(a : ℂ)‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [e, ← Real.sqrt_eq_rpow, Real.sqrt_sq h0]

/- English proof (translation)
Simplify using `[chC, ph]`.
-/
theorem chC_zero_ph (p : ℤ) (a : ℂˣ) : chC p 0 a = ph p a := by
  simp [chC, ph]

/- English proof (translation)
Simplify using `[chC]`.
-/
theorem chC_neg_one (p : ℤ) (s : ℂ) : chC p s (-1) = (-1) ^ p := by
  simp [chC]

/- English proof (translation)
Establish `hp : 0 < ‖(a : ℂ)‖` using `norm_pos_iff.2 a.ne_zero`. Establish `h1 : ‖((a : ℂ) / (‖(a : ℂ)‖ : ℂ))‖ = 1`. Rewrite using `[norm_div, Complex.norm_real, norm_norm, div_self hp.ne']`. Unfold `chC`. Rewrite using `[norm_mul, norm_zpow, h1, _root_.one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hp.le]`.

Evaluate the numerical expressions.
-/
theorem norm_chC (p : ℤ) (s : ℂ) (a : ℂˣ) : ‖chC p s a‖ = ‖(a : ℂ)‖ ^ (2 * s.re) := by
  have hp : 0 < ‖(a : ℂ)‖ := norm_pos_iff.2 a.ne_zero
  have h1 : ‖((a : ℂ) / (‖(a : ℂ)‖ : ℂ))‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self hp.ne']
  unfold chC
  rw [norm_mul, norm_zpow, h1, _root_.one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  norm_num

/- English proof (translation)
Establish `hv : Measurable (Units.val : ℂˣ → ℂ)` using `val_measEmb.measurable`. Unfold `chC`. Use `fun_prop`.
-/
theorem measurable_chC (p : ℤ) (s : ℂ) : Measurable (chC p s) := by
  have hv : Measurable (Units.val : ℂˣ → ℂ) := val_measEmb.measurable
  unfold chC
  fun_prop

/- English proof (translation)
Use `set F : ℂ → ℂ := fun z => ((‖z‖ ^ (2 * σ) * dd z : ℝ) : ℂ) with hF`. Establish `h` using `(integrable_mulC_iff F).2 (by`. Use `(wt_vol σ h0 h1).ofReal.congr ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with z hz`. Establish `hzp : 0 < ‖z‖` using `norm_pos_iff.2 hz`.

Simplify using `only [hF]`. Rewrite using `[← Complex.ofReal_mul]`. Use `congrArg _ ?_` and prove the remaining obligations. Use `show ‖z‖ ^ (2 * σ - 2) * dd z = (‖z‖ ^ 2)⁻¹ * (‖z‖ ^ (2 * σ) * dd z)`. Rewrite using `[Real.rpow_sub hzp, Real.rpow_two]`.

Use the proof step `ring)`. Use `h.norm.congr (Filter.Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `only [hF]`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg]`. Use `dd_pos (a : ℂ)` as an intermediate fact.

Check the signs of the components of the expression.
-/
theorem wt_int (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    Integrable (fun a : ℂˣ => ‖(a : ℂ)‖ ^ (2 * σ) * dd a) mulC := by
  set F : ℂ → ℂ := fun z => ((‖z‖ ^ (2 * σ) * dd z : ℝ) : ℂ) with hF
  have h := (integrable_mulC_iff F).2 (by
    refine (wt_vol σ h0 h1).ofReal.congr ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with z hz
    have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hF]
    rw [← Complex.ofReal_mul]
    refine congrArg _ ?_
    show ‖z‖ ^ (2 * σ - 2) * dd z = (‖z‖ ^ 2)⁻¹ * (‖z‖ ^ (2 * σ) * dd z)
    rw [Real.rpow_sub hzp, Real.rpow_two]
    ring)
  refine h.norm.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [hF]
  rw [Complex.norm_real, Real.norm_of_nonneg]
  have := dd_pos (a : ℂ)
  positivity

/- English proof (translation)
Establish `hv : Measurable (Units.val : ℂˣ → ℂ)` using `val_measEmb.measurable`. Establish `hW` using `((wt_int s.re h0 h1).mul_prod (wt_int s'.re h0' h1')).const_mul C`. Use `hW.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Establish `m1 : Measurable fun z : ℂˣ × ℂˣ => G z.1 z.2` using `hG.comp ((hv.comp measurable_fst).prodMk (hv.comp measurable_snd))`. Establish `m2 : Measurable fun z : ℂˣ × ℂˣ => chC p s z.1` using `(measurable_chC p s).comp measurable_fst`.

Establish `m3 : Measurable fun z : ℂˣ × ℂˣ => chC q s' z.2` using `(measurable_chC q s').comp measurable_snd`. Conclude with `((m1.mul m2).mul m3).aestronglyMeasurable`. Rewrite using `[norm_mul, norm_mul, norm_chC, norm_chC]`. Establish `h` using `hb z.1 z.2`. Establish `a1 : 0 ≤ ‖((z.1 : ℂˣ) : ℂ)‖ ^ (2 * s.re)` using `by positivity`.

Establish `a2 : 0 ≤ ‖((z.2 : ℂˣ) : ℂ)‖ ^ (2 * s'.re)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_int (G : ℂ → ℂ → ℂ) (hG : Measurable fun p : ℂ × ℂ => G p.1 p.2) (C : ℝ)
    (hb : ∀ x ξ, ‖G x ξ‖ ≤ C * (dd x * dd ξ)) (p q : ℤ) (s s' : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (h0' : 0 < s'.re) (h1' : s'.re < 1) :
    Integrable (fun z : ℂˣ × ℂˣ => G z.1 z.2 * chC p s z.1 * chC q s' z.2) (mulC.prod mulC) := by
  have hv : Measurable (Units.val : ℂˣ → ℂ) := val_measEmb.measurable
  have hW := ((wt_int s.re h0 h1).mul_prod (wt_int s'.re h0' h1')).const_mul C
  refine hW.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have m1 : Measurable fun z : ℂˣ × ℂˣ => G z.1 z.2 :=
      hG.comp ((hv.comp measurable_fst).prodMk (hv.comp measurable_snd))
    have m2 : Measurable fun z : ℂˣ × ℂˣ => chC p s z.1 := (measurable_chC p s).comp measurable_fst
    have m3 : Measurable fun z : ℂˣ × ℂˣ => chC q s' z.2 := (measurable_chC q s').comp measurable_snd
    exact ((m1.mul m2).mul m3).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_chC, norm_chC]
    have h := hb z.1 z.2
    have a1 : 0 ≤ ‖((z.1 : ℂˣ) : ℂ)‖ ^ (2 * s.re) := by positivity
    have a2 : 0 ≤ ‖((z.2 : ℂˣ) : ℂ)‖ ^ (2 * s'.re) := by positivity
    calc _ ≤ C * (dd z.1 * dd z.2) * ‖((z.1 : ℂˣ) : ℂ)‖ ^ (2 * s.re) * ‖((z.2 : ℂˣ) : ℂ)‖ ^ (2 * s'.re) := by gcongr
      _ = _ := by ring

/- English proof (translation)
Establish `p1 : MeasurePreserving (fun z : ℂˣ × ℂˣ => (z.2, z.1)) (mulC.prod mulC) (mulC.prod mulC)` using `Measure.measurePreserving_swap`. Establish `p2` using `measurePreserving_prod_mul (mulC) (mulC)`. Establish `p4 : MeasurePreserving (fun z : ℂˣ × ℂˣ => (z.1, z.2⁻¹)) (mulC.prod mulC) (mulC.prod mulC)` using `(MeasurePreserving.id mulC).prod mp_inv`. Establish `hT : MeasurePreserving (fun z : ℂˣ × ℂˣ => (z.2 * z.1, z.2⁻¹)) (mulC.prod mulC) (mulC.prod mulC)` using `((p4.comp p1).comp p2).comp p1`. Establish `hI : Integrable (fun z : ℂˣ × ℂˣ => H (z.2 * z.1, z.2⁻¹)) (mulC.prod mulC)` using `hT.integrable_comp hH.aestronglyMeasurable |>.2 hH`.

Rewrite using `[← integral_prod _ hH, ← integral_prod (fun z : ℂˣ × ℂˣ => H (z.2 * z.1, z.2⁻¹)) hI]`. Use `conv_rhs => rw [← hT.map_eq]`. Rewrite using `[integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hH.aestronglyMeasurable)]`.
-/
theorem shear (H : ℂˣ × ℂˣ → ℂ) (hH : Integrable H (mulC.prod mulC)) :
    ∫ a, ∫ t, H (t * a, t⁻¹) ∂mulC ∂mulC = ∫ x, ∫ ξ, H (x, ξ) ∂mulC ∂mulC := by
  have p1 : MeasurePreserving (fun z : ℂˣ × ℂˣ => (z.2, z.1)) (mulC.prod mulC) (mulC.prod mulC) :=
    Measure.measurePreserving_swap
  have p2 := measurePreserving_prod_mul (mulC) (mulC)
  have p4 : MeasurePreserving (fun z : ℂˣ × ℂˣ => (z.1, z.2⁻¹)) (mulC.prod mulC) (mulC.prod mulC) :=
    (MeasurePreserving.id mulC).prod mp_inv
  have hT : MeasurePreserving (fun z : ℂˣ × ℂˣ => (z.2 * z.1, z.2⁻¹)) (mulC.prod mulC) (mulC.prod mulC) :=
    ((p4.comp p1).comp p2).comp p1
  have hI : Integrable (fun z : ℂˣ × ℂˣ => H (z.2 * z.1, z.2⁻¹)) (mulC.prod mulC) :=
    hT.integrable_comp hH.aestronglyMeasurable |>.2 hH
  rw [← integral_prod _ hH, ← integral_prod (fun z : ℂˣ × ℂˣ => H (z.2 * z.1, z.2⁻¹)) hI]
  conv_rhs => rw [← hT.map_eq]
  rw [integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hH.aestronglyMeasurable)]

/- English proof (translation)
Unfold `W2`. Rewrite using `[Matrix.det_mul, ph_mul, norm_mul]`. Simplify using `only [Matrix.vecMul_vecMul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem whittaker_translate (k : ℕ) (f : (Fin 2 → ℂ) → ℂ) (M g : Matrix (Fin 2) (Fin 2) ℂ) :
    W2 k f (M * g) = ph (2 * (k : ℤ) - 2) g.det * ((‖g.det‖ : ℝ) : ℂ) *
      W2 k (fun v => f (Matrix.vecMul v g)) M := by
  unfold W2
  rw [Matrix.det_mul, ph_mul, norm_mul]
  simp only [Matrix.vecMul_vecMul]
  push_cast
  ring

/- English proof (translation)
Simplify using `[d2, Matrix.det_fin_two_of]`.
-/
theorem det_diagonal_alt (a : ℂ) : (d2 a).det = a := by
  simp [d2, Matrix.det_fin_two_of]

/- English proof (translation)
Simplify using `[w2, Matrix.det_fin_two_of]`.
-/
theorem det_weyl_element : w2.det = 1 := by
  simp [w2, Matrix.det_fin_two_of]

/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [d2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`.
-/
theorem vecMul_diagonal_alt (a t y : ℂ) : Matrix.vecMul ![t, t * y] (d2 a) = ![t * a, t * y] := by
  ext i
  fin_cases i <;> simp [d2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/- English proof (translation)
Unfold `W2`. Rewrite using `[det_diagonal_alt]`. Use `congr 1`. Establish `e` using `integral_mulC (fun z : ℂ => ph (4 * (k : ℤ) - 4) z * sF f (z * a) z⁻¹)`. Establish `e' : ∫ t : ℂˣ, ph (4 * (k : ℤ) - 4) t * sF f (t * a) (t⁻¹ : ℂˣ) ∂mulC = ∫ t : ℂˣ, ph (4 * (k : ℤ) - 4) t * sF f (t * a) (t : ℂ)⁻¹ ∂mulC`.

Simplify using `only [Units.val_inv_eq_inv_val]`. Rewrite using `[e', e]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht`. Establish `ht0 : t ≠ 0` using `ht`.

Simplify using `only [vecMul_diagonal_alt]`. Establish `h` using `integral_comp_mul t ht0 (fun u : ℂ => f ![t * a, u] * psiC (-(u * t⁻¹)))`. Establish `e2 : ∀ y : ℂ, t * y * t⁻¹ = y` using `fun y => by field_simp`. Simplify using `only [e2] at h`. Rewrite using `[h, sF]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem whittaker_diagonal (k : ℕ) (f : (Fin 2 → ℂ) → ℂ) (a : ℂˣ) :
    W2 k f (d2 a) = ph (2 * (k : ℤ) - 2) a * ((‖(a : ℂ)‖ : ℝ) : ℂ) *
      ∫ t : ℂˣ, ph (4 * (k : ℤ) - 4) t * sF f (t * a) (t⁻¹ : ℂˣ) ∂mulC := by
  unfold W2
  rw [det_diagonal_alt]
  congr 1
  have e := integral_mulC (fun z : ℂ => ph (4 * (k : ℤ) - 4) z * sF f (z * a) z⁻¹)
  have e' : ∫ t : ℂˣ, ph (4 * (k : ℤ) - 4) t * sF f (t * a) (t⁻¹ : ℂˣ) ∂mulC =
      ∫ t : ℂˣ, ph (4 * (k : ℤ) - 4) t * sF f (t * a) (t : ℂ)⁻¹ ∂mulC := by
    simp only [Units.val_inv_eq_inv_val]
  rw [e', e]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht
  have ht0 : t ≠ 0 := ht
  simp only [vecMul_diagonal_alt]
  have h := integral_comp_mul t ht0 (fun u : ℂ => f ![t * a, u] * psiC (-(u * t⁻¹)))
  have e2 : ∀ y : ℂ, t * y * t⁻¹ = y := fun y => by field_simp
  simp only [e2] at h
  rw [h, sF]
  ring

/- English proof (translation)
Unfold `fC volC`. Rewrite using `[integral_smul_measure]`. Simplify using the standard rewrite rules.
-/
theorem fC_eq (h : ℂ → ℂ) (w : ℂ) : fC h w = 2 * ∫ u : ℂ, h u * psiC (-(u * (-w))) := by
  unfold fC volC
  rw [integral_smul_measure]
  simp

/- English proof (translation)
Take `⟨C, hC, hb⟩` from `schw_bound f`. Use `⟨C, hC, fun x u => (hb x u).trans ?_⟩` and prove the remaining obligations. Establish `h1 : dd u ≤ 1` using `inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg u])`. Establish `hu` using `dd_pos u`. Establish `hx` using `dd_pos x`.

Establish `: dd u ^ 2 ≤ dd u` using `by nlinarith`. Use `gcongr`.
-/
theorem schw_bound' (f : SchwartzMap (Fin 2 → ℂ) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x u : ℂ, ‖f ![x, u]‖ ≤ C * (dd x * dd u) := by
  obtain ⟨C, hC, hb⟩ := schw_bound f
  refine ⟨C, hC, fun x u => (hb x u).trans ?_⟩
  have h1 : dd u ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg u])
  have hu := dd_pos u
  have hx := dd_pos x
  have : dd u ^ 2 ≤ dd u := by nlinarith
  gcongr

/- English proof (translation)
Rewrite using `[← mul_zpow]`. Simplify using the standard rewrite rules.
-/
theorem neg_one_sq (m : ℤ) : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
  rw [← mul_zpow]
  simp

/- English proof (translation)
Use `set h : ℂ → ℂ := fun u => f ![x, u] with hh`. Take `⟨C, hC, hb⟩` from `schw_bound' f`. Take `⟨C', hC', hb'⟩` from `sF_decay f`. Establish `hre : (1 - s).re = 1 - s.re` using `by simp`. Establish `h0' : 0 < (1 - s).re` using `by rw [hre]; linarith`.

Establish `h1' : (1 - s).re < 1` using `by rw [hre]; linarith`. Establish `hfC : ∀ w, fC h w = 2 * sF f x (-w)` using `fun w => fC_eq h w`. Establish `hxd` using `dd_pos x`. Establish `i2 : Integrable (fun w => h w * ((‖w‖ ^ (2 * ((1 - s).re - 1)) : ℝ) : ℂ))`. Establish `hW` using `(wt_vol (1 - s).re h0' h1').const_mul (C * dd x)`.

Use `hW.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Use `((continuous_slice f x).measurable.mul ?_).aestronglyMeasurable fun_prop` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), show 2 * ((1 - s).re - 1) = 2 * (1 - s).re - 2 by ring]`. Use `hb x w` as an intermediate fact. Establish `hp : 0 ≤ ‖w‖ ^ (2 * (1 - s).re - 2)` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Establish `i3 : Integrable (fun r => fC h r * ((‖r‖ ^ (-2 * (1 - s).re) : ℝ) : ℂ))`. Establish `hW` using `(wt_vol s.re h0 h1).const_mul (2 * (C' * dd x))`. Use `hW.mono' ?_ (Filter.Eventually.of_forall fun r => ?_)` and prove the remaining obligations. Establish `m1 : Measurable fun r : ℂ => sF f x (-r)` using `(measurable_sF f).comp (measurable_const.prodMk measurable_neg)`.

Establish `m2 : Measurable fun r : ℂ => fC h r`. Simplify using `only [hfC]`. Conclude with `m1.const_mul 2`. Use `(m2.mul ?_).aestronglyMeasurable` and prove the remaining obligations. Use `fun_prop`.

Rewrite using `[hfC, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hre, show -2 * (1 - s.re) = 2 * s.re - 2 by ring]`. Use `hb' x (-r)` as an intermediate fact. Establish `e : dd (-r) = dd r` using `by simp [dd]`. Rewrite `this` using `[e]`. Establish `hp : 0 ≤ ‖r‖ ^ (2 * s.re - 2)` using `by positivity`.

Establish `n2 : ‖(2 : ℂ)‖ = 2` using `by simp`. Rewrite using `[n2]`. Combine the equalities or inequalities in the displayed calculation. Establish `T` using `hT h (-m) (1 - s) h0' h1' (slice_int f x) i2 i3`. Rewrite `T` using `[neg_neg, sub_sub_cancel]`.

Unfold `z1 at T`. Use `set X : ℂ := ∫ ξ : ℂˣ, sF f x ξ * chC m s ξ ∂mulC with hX`. Establish `A : ∫ a : ℂˣ, fC h a * chC m s a ∂mulC = 2 * (-1) ^ m * X`. Establish `hinv` using `integral_mul_left_eq_self (μ := mulC) (fun a : ℂˣ => sF f x a * chC m s a) (-1 : ℂˣ)`. Rewrite using `[hX, ← hinv, ← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hfC, chC_mul, chC_neg_one]`. Establish `e : (((-1 : ℂˣ) * a : ℂˣ) : ℂ) = -(a : ℂ)` using `by simp`. Rewrite using `[e]`.

Take the linear combination `(-(2 * sF f x (-(a : ℂ)) * chC m s a)) * neg_one_sq m`. Rewrite `T` using `[A]`. Establish `hZ : ∫ u : ℂˣ, f ![x, u] * chC (-m) (1 - s) u ∂mulC = ∫ a : ℂˣ, h a * chC (-m) (1 - s) a ∂mulC` using `rfl`. Rewrite using `[hZ]`. Take the linear combination `((1 / 2 : ℂ) * (-1) ^ m) * T - X * neg_one_sq m`.
-/
theorem tate_slice (hT : TateFunctionalEquationComplex) (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x : ℂ) (m : ℤ) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∫ ξ : ℂˣ, sF f x ξ * chC m s ξ ∂mulC =
      (1 / 2) * (-1) ^ m * gC (-m) (1 - s) * ∫ u : ℂˣ, f ![x, u] * chC (-m) (1 - s) u ∂mulC := by
  set h : ℂ → ℂ := fun u => f ![x, u] with hh
  obtain ⟨C, hC, hb⟩ := schw_bound' f
  obtain ⟨C', hC', hb'⟩ := sF_decay f
  have hre : (1 - s).re = 1 - s.re := by simp
  have h0' : 0 < (1 - s).re := by rw [hre]; linarith
  have h1' : (1 - s).re < 1 := by rw [hre]; linarith
  have hfC : ∀ w, fC h w = 2 * sF f x (-w) := fun w => fC_eq h w
  have hxd := dd_pos x
  have i2 : Integrable (fun w => h w * ((‖w‖ ^ (2 * ((1 - s).re - 1)) : ℝ) : ℂ)) := by
    have hW := (wt_vol (1 - s).re h0' h1').const_mul (C * dd x)
    refine hW.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · refine ((continuous_slice f x).measurable.mul ?_).aestronglyMeasurable
      fun_prop
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        show 2 * ((1 - s).re - 1) = 2 * (1 - s).re - 2 by ring]
      have := hb x w
      have hp : 0 ≤ ‖w‖ ^ (2 * (1 - s).re - 2) := by positivity
      calc _ ≤ C * (dd x * dd w) * ‖w‖ ^ (2 * (1 - s).re - 2) := by gcongr
        _ = _ := by ring
  have i3 : Integrable (fun r => fC h r * ((‖r‖ ^ (-2 * (1 - s).re) : ℝ) : ℂ)) := by
    have hW := (wt_vol s.re h0 h1).const_mul (2 * (C' * dd x))
    refine hW.mono' ?_ (Filter.Eventually.of_forall fun r => ?_)
    · have m1 : Measurable fun r : ℂ => sF f x (-r) :=
        (measurable_sF f).comp (measurable_const.prodMk measurable_neg)
      have m2 : Measurable fun r : ℂ => fC h r := by
        simp only [hfC]
        exact m1.const_mul 2
      refine (m2.mul ?_).aestronglyMeasurable
      fun_prop
    · rw [hfC, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hre,
        show -2 * (1 - s.re) = 2 * s.re - 2 by ring]
      have := hb' x (-r)
      have e : dd (-r) = dd r := by simp [dd]
      rw [e] at this
      have hp : 0 ≤ ‖r‖ ^ (2 * s.re - 2) := by positivity
      have n2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [n2]
      calc _ ≤ 2 * (C' * (dd x * dd r)) * ‖r‖ ^ (2 * s.re - 2) := by gcongr
        _ = _ := by ring
  have T := hT h (-m) (1 - s) h0' h1' (slice_int f x) i2 i3
  rw [neg_neg, sub_sub_cancel] at T
  unfold z1 at T
  set X : ℂ := ∫ ξ : ℂˣ, sF f x ξ * chC m s ξ ∂mulC with hX
  have A : ∫ a : ℂˣ, fC h a * chC m s a ∂mulC = 2 * (-1) ^ m * X := by
    have hinv := integral_mul_left_eq_self (μ := mulC) (fun a : ℂˣ => sF f x a * chC m s a) (-1 : ℂˣ)
    rw [hX, ← hinv, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [hfC, chC_mul, chC_neg_one]
    have e : (((-1 : ℂˣ) * a : ℂˣ) : ℂ) = -(a : ℂ) := by simp
    rw [e]
    linear_combination (-(2 * sF f x (-(a : ℂ)) * chC m s a)) * neg_one_sq m
  rw [A] at T
  have hZ : ∫ u : ℂˣ, f ![x, u] * chC (-m) (1 - s) u ∂mulC = ∫ a : ℂˣ, h a * chC (-m) (1 - s) a ∂mulC := rfl
  rw [hZ]
  linear_combination ((1 / 2 : ℂ) * (-1) ^ m) * T - X * neg_one_sq m

/- English proof (translation)
Rewrite using `[← chC_half, chC_add, chC_mul, chC_inv, ← chC_zero_ph]`. Establish `e : chC (n + p) s t * chC (n + p) s a * chC (-(n - p)) (-s) t = (chC (n + p) s t * chC (-(n - p)) (-s) t) * chC (n + p) s a` using `by ring`. Rewrite using `[e, chC_add, mul_comm]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chi_id (p n : ℤ) (s : ℂ) (a t : ℂˣ) :
    ph p a * ((‖(a : ℂ)‖ : ℝ) : ℂ) * chC n (s - 1 / 2) a * ph (2 * p) t =
      chC (n + p) s (t * a) * chC (n - p) s t⁻¹ := by
  rw [← chC_half, chC_add, chC_mul, chC_inv, ← chC_zero_ph]
  have e : chC (n + p) s t * chC (n + p) s a * chC (-(n - p)) (-s) t =
      (chC (n + p) s t * chC (-(n - p)) (-s) t) * chC (n + p) s a := by ring
  rw [e, chC_add, mul_comm]
  congr 2
  · ring
  · ring
  · ring
  · ring

/- English proof (translation)
Use `set p : ℤ := 2 * (k : ℤ) - 2 with hp`. Take `⟨C, -, hb⟩` from `sF_decay f`. Use `set H : ℂˣ × ℂˣ → ℂ := fun z => sF f z.1 z.2 * chC (n + p) s z.1 * chC (n - p) s z.2 with hH`. Establish `hI : Integrable H (mulC.prod mulC)` using `prod_int (sF f) (measurable_sF f) C hb (n + p) (n - p) s s h0 h1 h0 h1`. Establish `s1 : ∀ a : ℂˣ, W2 k f (d2 a) * chC n (s - 1 / 2) a = ∫ t, H (t * a, t⁻¹) ∂mulC`.

Introduce `a`. Rewrite using `[whittaker_diagonal, mul_right_comm, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [hH]`. Establish `e` using `chi_id p n s a t`.

Rewrite using `[show (4 * (k : ℤ) - 4) = 2 * p by rw [hp]; ring]`. Simplify using `only [Units.val_mul] at e ⊢`. Take the linear combination `(sF f ((t : ℂ) * a) ((t⁻¹ : ℂˣ) : ℂ)) * e`. Simplify using `only [s1]`. Rewrite using `[shear H hI, ← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [hH]`. Establish `e : ∀ ξ : ℂˣ, sF f x ξ * chC (n + p) s x * chC (n - p) s ξ = chC (n + p) s x * (sF f x ξ * chC (n - p) s ξ)` using `fun ξ => by ring`. Simplify using `only [e]`. Rewrite using `[integral_const_mul, tate_slice hT f x (n - p) s h0 h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem key (hT : TateFunctionalEquationComplex) (k : ℕ) (f : SchwartzMap (Fin 2 → ℂ) ℂ) (n : ℤ) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∫ a : ℂˣ, W2 k f (d2 a) * chC n (s - 1 / 2) a ∂mulC =
      (1 / 2) * (-1) ^ (n - (2 * (k : ℤ) - 2)) * gC (-(n - (2 * (k : ℤ) - 2))) (1 - s) *
        ∫ x : ℂˣ, chC (n + (2 * (k : ℤ) - 2)) s x *
          ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC (-(n - (2 * (k : ℤ) - 2))) (1 - s) u ∂mulC ∂mulC := by
  set p : ℤ := 2 * (k : ℤ) - 2 with hp
  obtain ⟨C, -, hb⟩ := sF_decay f
  set H : ℂˣ × ℂˣ → ℂ := fun z => sF f z.1 z.2 * chC (n + p) s z.1 * chC (n - p) s z.2 with hH
  have hI : Integrable H (mulC.prod mulC) :=
    prod_int (sF f) (measurable_sF f) C hb (n + p) (n - p) s s h0 h1 h0 h1
  have s1 : ∀ a : ℂˣ, W2 k f (d2 a) * chC n (s - 1 / 2) a = ∫ t, H (t * a, t⁻¹) ∂mulC := by
    intro a
    rw [whittaker_diagonal, mul_right_comm, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hH]
    have e := chi_id p n s a t
    rw [show (4 * (k : ℤ) - 4) = 2 * p by rw [hp]; ring]
    simp only [Units.val_mul] at e ⊢
    linear_combination (sF f ((t : ℂ) * a) ((t⁻¹ : ℂˣ) : ℂ)) * e
  simp only [s1]
  rw [shear H hI, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hH]
  have e : ∀ ξ : ℂˣ, sF f x ξ * chC (n + p) s x * chC (n - p) s ξ =
      chC (n + p) s x * (sF f x ξ * chC (n - p) s ξ) := fun ξ => by ring
  simp only [e]
  rw [integral_const_mul, tate_slice hT f x (n - p) s h0 h1]
  ring

/- English proof (translation)
Simplify using `[gC, Int.natAbs_neg]`.
-/
theorem gC_neg (m : ℤ) (s : ℂ) : gC (-m) s = gC m s := by
  simp [gC, Int.natAbs_neg]

/- English proof (translation)
Rewrite using `[Complex.Gammaℂ_def]`. Use `mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hz)` and prove the remaining obligations. Rewrite using `[Ne, Complex.cpow_eq_zero_iff]`. Simplify using `[Real.pi_ne_zero]`.
-/
theorem gam_ne {z : ℂ} (hz : 0 < z.re) : Complex.Gammaℂ z ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hz)
  rw [Ne, Complex.cpow_eq_zero_iff]
  simp [Real.pi_ne_zero]

/- English proof (translation)
Use `set A : ℕ := m.natAbs with hA`. Establish `hA0 : (0 : ℝ) ≤ (A : ℝ) / 2` using `by positivity`. Establish `g1 : Complex.Gammaℂ (s + (A : ℂ) / 2) ≠ 0` using `gam_ne (by`. Establish `: (s + (A : ℂ) / 2).re = s.re + (A : ℝ) / 2` using `by simp`. Rewrite using `[this]`.

Use the proof step `linarith)`. Establish `g2 : Complex.Gammaℂ (1 - s + (A : ℂ) / 2) ≠ 0` using `gam_ne (by`. Establish `: (1 - s + (A : ℂ) / 2).re = 1 - s.re + (A : ℝ) / 2` using `by simp`. Rewrite using `[this]`. Use the proof step `linarith)`.

Establish `hprod : gC m s * gC m (1 - s) = (-1 : ℂ) ^ A`. Unfold `gC`. Rewrite using `[← hA, sub_sub_cancel]`. Establish `: ((-Complex.I) ^ A) * ((-Complex.I) ^ A) = (-1 : ℂ) ^ A`. Rewrite using `[← mul_pow]`.

Simplify using the standard rewrite rules. Rewrite using `[← this]`. Generalize the expression as in `Complex.Gammaℂ (1 - s + (A : ℂ) / 2) = G1 at g2 ⊢`. Generalize the expression as in `Complex.Gammaℂ (s + (A : ℂ) / 2) = G2 at g1 ⊢`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hprod]`. Take `⟨q, hq | hq⟩` from `Int.eq_nat_or_neg m`. Establish `: A = q` using `by rw [hA, hq]; simp`. Rewrite using `[this, hq, zpow_natCast, ← mul_pow]`. Simplify using the standard rewrite rules.

Establish `: A = q` using `by rw [hA, hq]; simp`. Rewrite using `[this, hq, _root_.zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]`. Simplify using `[← mul_pow]`.
-/
theorem gC_refl (m : ℤ) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    (-1 : ℂ) ^ m * (gC m s * gC m (1 - s)) = 1 := by
  set A : ℕ := m.natAbs with hA
  have hA0 : (0 : ℝ) ≤ (A : ℝ) / 2 := by positivity
  have g1 : Complex.Gammaℂ (s + (A : ℂ) / 2) ≠ 0 :=
    gam_ne (by
      have : (s + (A : ℂ) / 2).re = s.re + (A : ℝ) / 2 := by simp
      rw [this]
      linarith)
  have g2 : Complex.Gammaℂ (1 - s + (A : ℂ) / 2) ≠ 0 :=
    gam_ne (by
      have : (1 - s + (A : ℂ) / 2).re = 1 - s.re + (A : ℝ) / 2 := by simp
      rw [this]
      linarith)
  have hprod : gC m s * gC m (1 - s) = (-1 : ℂ) ^ A := by
    unfold gC
    rw [← hA, sub_sub_cancel]
    have : ((-Complex.I) ^ A) * ((-Complex.I) ^ A) = (-1 : ℂ) ^ A := by
      rw [← mul_pow]
      simp
    rw [← this]
    generalize Complex.Gammaℂ (1 - s + (A : ℂ) / 2) = G1 at g2 ⊢
    generalize Complex.Gammaℂ (s + (A : ℂ) / 2) = G2 at g1 ⊢
    field_simp
  rw [hprod]
  obtain ⟨q, hq | hq⟩ := Int.eq_nat_or_neg m
  · have : A = q := by rw [hA, hq]; simp
    rw [this, hq, zpow_natCast, ← mul_pow]
    simp
  · have : A = q := by rw [hA, hq]; simp
    rw [this, hq, _root_.zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
    simp [← mul_pow]

/- English proof (translation)
Establish `hu : IsUnit g.det` using `isUnit_iff_ne_zero.2 hg`. Set `e : (Fin 2 → ℂ) ≃ₗ[ℝ] (Fin 2 → ℂ)` to `{ toFun := fun v => Matrix.vecMul v g map_add' := fun a b => Matrix.add_vecMul g a b map_smul' := fun c a => Matrix.smul_vecMul c a g invFun := fun v => Matrix.vecMul v g⁻¹ left_inv := fun v => by`. Simplify using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv g hu]`. Use `right_inv := fun v => by`. Simplify using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul g hu] }`.

Conclude with `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv f, fun v => rfl⟩`.
-/
theorem exists_translate (f : SchwartzMap (Fin 2 → ℂ) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) :
    ∃ f1 : SchwartzMap (Fin 2 → ℂ) ℂ, ∀ v, f1 v = f (Matrix.vecMul v g) := by
  have hu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  let e : (Fin 2 → ℂ) ≃ₗ[ℝ] (Fin 2 → ℂ) :=
    { toFun := fun v => Matrix.vecMul v g
      map_add' := fun a b => Matrix.add_vecMul g a b
      map_smul' := fun c a => Matrix.smul_vecMul c a g
      invFun := fun v => Matrix.vecMul v g⁻¹
      left_inv := fun v => by
        simp [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv g hu]
      right_inv := fun v => by
        simp [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul g hu] }
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv f, fun v => rfl⟩

/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [w2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`.
-/
theorem vecMul_weyl_element (x u : ℂ) : Matrix.vecMul ![x, u] w2 = ![-u, x] := by
  ext i
  fin_cases i <;> simp [w2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/- English proof (translation)
Take `⟨C, -, hb⟩` from `schw_bound' f`. Establish `hm : Measurable fun p : ℂ × ℂ => f ![p.1, p.2]` using `(f.continuous.comp continuous_vec).measurable`. Establish `hI` using `prod_int (fun x u => f ![x, u]) hm C hb r q s s' h0 h1 h0' h1'`. Establish `inner : ∀ x : ℂˣ, ∫ u : ℂˣ, f ![-(u : ℂ), (x : ℂ)] * chC r s u ∂mulC = (-1) ^ r * ∫ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s u ∂mulC`. Introduce `x`.

Establish `hinv` using `integral_mul_left_eq_self (μ := mulC) (fun u : ℂˣ => f ![(u : ℂ), (x : ℂ)] * chC r s ((-1 : ℂˣ) * u)) (-1 : ℂˣ)`. Establish `e1 : ∀ u : ℂˣ, f ![(((-1 : ℂˣ) * u : ℂˣ) : ℂ), (x : ℂ)] * chC r s ((-1 : ℂˣ) * ((-1 : ℂˣ) * u)) = f ![-(u : ℂ), (x : ℂ)] * chC r s u`. Introduce `u`. Establish `e : (((-1 : ℂˣ) * u : ℂˣ) : ℂ) = -(u : ℂ)` using `by simp`. Rewrite using `[e]`.

Simplify using the standard rewrite rules. Establish `e2 : ∀ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s ((-1 : ℂˣ) * u) = (-1) ^ r * (f ![(u : ℂ), (x : ℂ)] * chC r s u)`. Introduce `u`. Rewrite using `[chC_mul, chC_neg_one]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e1, e2] at hinv`. Rewrite using `[hinv, integral_const_mul]`. Simplify using `only [inner]`. Rewrite using `[← integral_const_mul]`. Establish `hsw` using `integral_integral_swap (μ := mulC) (ν := mulC) (f := fun u x : ℂˣ => f ![(u : ℂ), (x : ℂ)] * chC r s u * chC q s' x) hI`.

Establish `l : ∀ x : ℂˣ, chC q s' x * ((-1) ^ r * ∫ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s u ∂mulC) = (-1) ^ r * ∫ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s u * chC q s' x ∂mulC`. Introduce `x`. Rewrite using `[integral_mul_const]`. Expand and normalize the polynomial expressions, which then agree. Establish `r' : ∀ x : ℂˣ, chC r s x * ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC q s' u ∂mulC = ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC r s x * chC q s' u ∂mulC`.

Introduce `x`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [l, r']`. Rewrite using `[integral_const_mul, integral_const_mul, ← hsw]`.
-/
theorem swap_I (f : SchwartzMap (Fin 2 → ℂ) ℂ) (q r : ℤ) (s s' : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (h0' : 0 < s'.re) (h1' : s'.re < 1) :
    ∫ x : ℂˣ, chC q s' x * ∫ u : ℂˣ, f ![-(u : ℂ), (x : ℂ)] * chC r s u ∂mulC ∂mulC =
      (-1) ^ r * ∫ x : ℂˣ, chC r s x * ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC q s' u ∂mulC ∂mulC := by
  obtain ⟨C, -, hb⟩ := schw_bound' f
  have hm : Measurable fun p : ℂ × ℂ => f ![p.1, p.2] := (f.continuous.comp continuous_vec).measurable
  have hI := prod_int (fun x u => f ![x, u]) hm C hb r q s s' h0 h1 h0' h1'
  have inner : ∀ x : ℂˣ, ∫ u : ℂˣ, f ![-(u : ℂ), (x : ℂ)] * chC r s u ∂mulC =
      (-1) ^ r * ∫ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s u ∂mulC := by
    intro x
    have hinv := integral_mul_left_eq_self (μ := mulC)
      (fun u : ℂˣ => f ![(u : ℂ), (x : ℂ)] * chC r s ((-1 : ℂˣ) * u)) (-1 : ℂˣ)
    have e1 : ∀ u : ℂˣ, f ![(((-1 : ℂˣ) * u : ℂˣ) : ℂ), (x : ℂ)] * chC r s ((-1 : ℂˣ) * ((-1 : ℂˣ) * u)) =
        f ![-(u : ℂ), (x : ℂ)] * chC r s u := by
      intro u
      have e : (((-1 : ℂˣ) * u : ℂˣ) : ℂ) = -(u : ℂ) := by simp
      rw [e]
      simp
    have e2 : ∀ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s ((-1 : ℂˣ) * u) =
        (-1) ^ r * (f ![(u : ℂ), (x : ℂ)] * chC r s u) := by
      intro u
      rw [chC_mul, chC_neg_one]
      ring
    simp only [e1, e2] at hinv
    rw [hinv, integral_const_mul]
  simp only [inner]
  rw [← integral_const_mul]
  have hsw := integral_integral_swap (μ := mulC) (ν := mulC)
    (f := fun u x : ℂˣ => f ![(u : ℂ), (x : ℂ)] * chC r s u * chC q s' x) hI
  have l : ∀ x : ℂˣ, chC q s' x * ((-1) ^ r * ∫ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s u ∂mulC) =
      (-1) ^ r * ∫ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s u * chC q s' x ∂mulC := by
    intro x
    rw [integral_mul_const]
    ring
  have r' : ∀ x : ℂˣ, chC r s x * ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC q s' u ∂mulC =
      ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC r s x * chC q s' u ∂mulC := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring
  simp only [l, r']
  rw [integral_const_mul, integral_const_mul, ← hsw]

/- English proof (translation)
Introduce `hT k hk f n s g hg h0 h1`. Establish `hre : (1 - s).re = 1 - s.re` using `by simp`. Establish `h0' : 0 < (1 - s).re` using `by rw [hre]; linarith`. Establish `h1' : (1 - s).re < 1` using `by rw [hre]; linarith`. Take `⟨f1, hf1⟩` from `exists_translate f g hg`.

Take `⟨f2, hf2⟩` from `exists_translate f1 w2 (by rw [det_weyl_element]; exact one_ne_zero)`. Establish `hf1' : (fun v => f (Matrix.vecMul v g)) = ⇑f1` using `funext fun v => (hf1 v).symm`. Establish `hf2' : (fun v => f1 (Matrix.vecMul v w2)) = ⇑f2` using `funext fun v => (hf2 v).symm`. Use `set c : ℂ := ph (2 * (k : ℤ) - 2) g.det * ((‖g.det‖ : ℝ) : ℂ) with hc`. Use `set p : ℤ := 2 * (k : ℤ) - 2 with hp`.

Establish `hph1 : ph p 1 = 1` using `by simp [ph]`. Establish `z1e : z2 k n s f g = c * ∫ a : ℂˣ, W2 k f1 (d2 a) * chC n (s - 1 / 2) a ∂mulC`. Unfold `z2`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[whittaker_translate, hf1', ← hp, ← hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `z2e : z2' k n s f g = c * ∫ a : ℂˣ, W2 k f2 (d2 a) * chC (-n) ((1 - s) - 1 / 2) a ∂mulC`. Unfold `z2'`.

Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[whittaker_translate, hf1', whittaker_translate, hf2', det_weyl_element, ← hp, ← hc, hph1, show (1 - s - 1 / 2 : ℂ) = 1 / 2 - s by ring]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `K1` using `key hT k f1 n s h0 h1`. Establish `K2` using `key hT k f2 (-n) (1 - s) h0' h1'`. Rewrite `K1`, `K2` using `[← hp]`. Establish `e1 : -n - p = -(n + p)` using `by ring`.

Establish `e2 : -n + p = -(n - p)` using `by ring`. Rewrite `K2` using `[e1, e2, neg_neg, sub_sub_cancel]`. Simplify using `only [hf2, vecMul_weyl_element] at K2`. Rewrite `K2` using `[swap_I f1 (-(n - p)) (n + p) s (1 - s) h0 h1 h0' h1']`. Rewrite `K1` using `[gC_neg]`.

Establish `G` using `gC_refl (n - p) s h0 h1`. Establish `hN : ((-1 : ℂ) ^ (-(n + p))) * (-1) ^ (n + p) = 1`. Rewrite using `[_root_.zpow_neg]`. Conclude with `inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num))`. Establish `hcast : 2 * ((k - 1 : ℕ) : ℤ) = p`.

Rewrite using `[hp]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[z1e, z2e, K1, K2, g2, hcast]`. Generalize the expression as in `(∫ x : ℂˣ, chC (n + p) s x * ∫ u : ℂˣ, f1 ![(x : ℂ), (u : ℂ)] * chC (-(n - p)) (1 - s) u ∂mulC ∂mulC) = Iv`. Take the linear combination `(c * (1 / 2) * gC (n + p) s * Iv) * hN - (c * (1 / 2) * gC (n + p) s * Iv) * G`.
-/
theorem main : TateFunctionalEquationComplex → FunctionalEquationGL2GL1Complex := by
  intro hT k hk f n s g hg h0 h1
  have hre : (1 - s).re = 1 - s.re := by simp
  have h0' : 0 < (1 - s).re := by rw [hre]; linarith
  have h1' : (1 - s).re < 1 := by rw [hre]; linarith
  obtain ⟨f1, hf1⟩ := exists_translate f g hg
  obtain ⟨f2, hf2⟩ := exists_translate f1 w2 (by rw [det_weyl_element]; exact one_ne_zero)
  have hf1' : (fun v => f (Matrix.vecMul v g)) = ⇑f1 := funext fun v => (hf1 v).symm
  have hf2' : (fun v => f1 (Matrix.vecMul v w2)) = ⇑f2 := funext fun v => (hf2 v).symm
  set c : ℂ := ph (2 * (k : ℤ) - 2) g.det * ((‖g.det‖ : ℝ) : ℂ) with hc
  set p : ℤ := 2 * (k : ℤ) - 2 with hp
  have hph1 : ph p 1 = 1 := by simp [ph]
  have z1e : z2 k n s f g = c * ∫ a : ℂˣ, W2 k f1 (d2 a) * chC n (s - 1 / 2) a ∂mulC := by
    unfold z2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [whittaker_translate, hf1', ← hp, ← hc]
    ring
  have z2e : z2' k n s f g = c * ∫ a : ℂˣ, W2 k f2 (d2 a) * chC (-n) ((1 - s) - 1 / 2) a ∂mulC := by
    unfold z2'
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [whittaker_translate, hf1', whittaker_translate, hf2', det_weyl_element, ← hp, ← hc, hph1,
      show (1 - s - 1 / 2 : ℂ) = 1 / 2 - s by ring]
    simp
    ring
  have K1 := key hT k f1 n s h0 h1
  have K2 := key hT k f2 (-n) (1 - s) h0' h1'
  rw [← hp] at K1 K2
  have e1 : -n - p = -(n + p) := by ring
  have e2 : -n + p = -(n - p) := by ring
  rw [e1, e2, neg_neg, sub_sub_cancel] at K2
  simp only [hf2, vecMul_weyl_element] at K2
  rw [swap_I f1 (-(n - p)) (n + p) s (1 - s) h0 h1 h0' h1'] at K2
  rw [gC_neg] at K1
  have G := gC_refl (n - p) s h0 h1
  have hN : ((-1 : ℂ) ^ (-(n + p))) * (-1) ^ (n + p) = 1 := by
    rw [_root_.zpow_neg]
    exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num))
  have hcast : 2 * ((k - 1 : ℕ) : ℤ) = p := by
    rw [hp]
    omega
  rw [z1e, z2e, K1, K2, g2, hcast]
  generalize (∫ x : ℂˣ, chC (n + p) s x *
    ∫ u : ℂˣ, f1 ![(x : ℂ), (u : ℂ)] * chC (-(n - p)) (1 - s) u ∂mulC ∂mulC) = Iv
  linear_combination (c * (1 / 2) * gC (n + p) s * Iv) * hN - (c * (1 / 2) * gC (n + p) s * Iv) * G

end GlobalTheory.CompanionTheory.GodementFE
