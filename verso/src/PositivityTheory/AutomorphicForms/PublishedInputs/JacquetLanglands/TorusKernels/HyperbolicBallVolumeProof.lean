import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.HyperbolicBallVolume

open UpperTheory.Esk

def F (y : ℝ) : ℝ := (1 + y ^ (-(1 / 2 : ℝ))) / (1 + y) ^ 2

/- English proof (translation)
Establish `hm : Measurable F` using `by unfold F; fun_prop`. Establish `h1 : IntegrableOn F (Ioo 0 2)`. Establish `hg : IntegrableOn (fun y : ℝ => 1 + y ^ (-(1 / 2 : ℝ))) (Ioo 0 2)` using `(integrableOn_const (by simp)).add ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).2 (by norm_num))`. Use `hg.mono' hm.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_)` and prove the remaining obligations.

Establish `hy0 : 0 < y` using `hy.1`. Establish `hp : 0 ≤ y ^ (-(1 / 2 : ℝ))` using `Real.rpow_nonneg hy0.le _`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity)]`. Unfold `F`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Use polynomial arithmetic with `[sq_nonneg y]`. Establish `h2 : IntegrableOn F (Ioi 1)`. Establish `hg : IntegrableOn (fun y : ℝ => 2 * y ^ (-2 : ℝ)) (Ioi 1)` using `(integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 2`. Use `hg.mono' hm.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)` and prove the remaining obligations.

Establish `hy1 : (1 : ℝ) < y` using `hy`. Establish `hy0 : 0 < y` using `by linarith`. Establish `hp : y ^ (-(1 / 2 : ℝ)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by norm_num)`. Establish `hp0 : 0 ≤ y ^ (-(1 / 2 : ℝ))` using `Real.rpow_nonneg hy0.le _`. Establish `e : y ^ (-2 : ℝ) = 1 / y ^ 2`.

Rewrite using `[Real.rpow_neg hy0.le, one_div]`. Use `norm_cast`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity), e]`. Unfold `F`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Establish `: 2 ≤ 2 * (1 / y ^ 2) * (1 + y) ^ 2`. Rewrite using `[mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(h1.union h2).mono_set (fun y (hy : 0 < y) => by`. Distinguish the cases in `h : y < 2`.

Conclude with `Or.inl ⟨hy, h⟩`. Conclude with `Or.inr (show (1 : ℝ) < y by linarith))`.
-/
theorem F_int : IntegrableOn F (Ioi 0) := by
  have hm : Measurable F := by unfold F; fun_prop
  have h1 : IntegrableOn F (Ioo 0 2) := by
    have hg : IntegrableOn (fun y : ℝ => 1 + y ^ (-(1 / 2 : ℝ))) (Ioo 0 2) :=
      (integrableOn_const (by simp)).add ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).2 (by norm_num))
    refine hg.mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy0 : 0 < y := hy.1
    have hp : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hy0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity)]
    unfold F
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg y]
  have h2 : IntegrableOn F (Ioi 1) := by
    have hg : IntegrableOn (fun y : ℝ => 2 * y ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 2
    refine hg.mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : 0 < y := by linarith
    have hp : y ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by norm_num)
    have hp0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hy0.le _
    have e : y ^ (-2 : ℝ) = 1 / y ^ 2 := by
      rw [Real.rpow_neg hy0.le, one_div]; norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity), e]
    unfold F
    rw [div_le_iff₀ (by positivity)]
    have : 2 ≤ 2 * (1 / y ^ 2) * (1 + y) ^ 2 := by
      rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
    linarith
  exact (h1.union h2).mono_set (fun y (hy : 0 < y) => by
    by_cases h : y < 2
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr (show (1 : ℝ) < y by linarith))

def A : ℝ≥0∞ := ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2)⁻¹)

/- English proof (translation)
The claim follows from `integrable_inv_one_add_sq.lintegral_lt_top`.
-/
theorem A_lt : A < ∞ := integrable_inv_one_add_sq.lintegral_lt_top

/- English proof (translation)
Establish `h` using `Real.map_volume_mul_left hy.ne'`. Establish `hm : Measurable fun x : ℝ => ENNReal.ofReal ((1 + x ^ 2)⁻¹)` using `by fun_prop`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h, lintegral_smul_measure, smul_eq_mul, abs_of_pos (inv_pos.2 hy), A]`.
-/
theorem x_int {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + (y * x) ^ 2)⁻¹) = ENNReal.ofReal y⁻¹ * A := by
  have h := Real.map_volume_mul_left hy.ne'
  have hm : Measurable fun x : ℝ => ENNReal.ofReal ((1 + x ^ 2)⁻¹) := by fun_prop
  calc ∫⁻ x : ℝ, ENNReal.ofReal ((1 + (y * x) ^ 2)⁻¹)
      = ∫⁻ x, ENNReal.ofReal ((1 + x ^ 2)⁻¹) ∂(Measure.map (y * ·) volume) :=
        (lintegral_map hm (measurable_const_mul y)).symm
    _ = ENNReal.ofReal y⁻¹ * A := by
        rw [h, lintegral_smul_measure, smul_eq_mul, abs_of_pos (inv_pos.2 hy), A]

/- English proof (translation)
Establish `hn : ‖iP.1 - conj (pt x y hy.ne').1‖ ^ 2 = (y * x) ^ 2 + (1 + y) ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[iP, pt]`. Expand and normalize the polynomial expressions, which then agree. Establish `him : 0 < iP.1.im * (pt x y hy.ne').1.im` using `by simp [iP, pt, hy]`.

Rewrite using `[kap, if_pos him, hn]`. Simplify using `[iP, pt]`.
-/
theorem kap_pt {x y : ℝ} (hy : 0 < y) :
    kap iP (pt x y hy.ne') = 4 * y / ((y * x) ^ 2 + (1 + y) ^ 2) := by
  have hn : ‖iP.1 - conj (pt x y hy.ne').1‖ ^ 2 = (y * x) ^ 2 + (1 + y) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [iP, pt]; ring
  have him : 0 < iP.1.im * (pt x y hy.ne').1.im := by simp [iP, pt, hy]
  rw [kap, if_pos him, hn]
  simp [iP, pt]

/- English proof (translation)
Rewrite using `[kap, if_neg]`. Simplify using `[iP]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kap_neg (w : P) (hw : w.1.im < 0) : kap iP w = 0 := by
  rw [kap, if_neg]
  simp [iP]; linarith

/- English proof (translation)
Rewrite using `[kap_pt hy]`. Use `set D := (y * x) ^ 2 + (1 + y) ^ 2`. Establish `hD1 : 1 + (y * x) ^ 2 ≤ D` using `by simp only [D]; nlinarith`. Establish `hD2 : (1 + y) ^ 2 ≤ D` using `by simp only [D]; nlinarith [sq_nonneg (y * x)]`. Establish `hp : 0 < 1 + (y * x) ^ 2` using `by positivity`.

Establish `hq : 0 < (1 + y) ^ 2` using `by positivity`. Establish `e : 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ = (4 * y) ^ 2 / ((1 + (y * x) ^ 2) * (1 + y) ^ 2)` using `by field_simp; ring`. Rewrite using `[e, div_pow]`. Apply `div_le_div_of_nonneg_left (by positivity) (by positivity)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem kap_sq_le {x y : ℝ} (hy : 0 < y) :
    kap iP (pt x y hy.ne') ^ 2 ≤ 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ := by
  rw [kap_pt hy]
  set D := (y * x) ^ 2 + (1 + y) ^ 2
  have hD1 : 1 + (y * x) ^ 2 ≤ D := by simp only [D]; nlinarith
  have hD2 : (1 + y) ^ 2 ≤ D := by simp only [D]; nlinarith [sq_nonneg (y * x)]
  have hp : 0 < 1 + (y * x) ^ 2 := by positivity
  have hq : 0 < (1 + y) ^ 2 := by positivity
  have e : 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ = (4 * y) ^ 2 / ((1 + (y * x) ^ 2) * (1 + y) ^ 2) := by
    field_simp; ring
  rw [e, div_pow]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc (1 + (y * x) ^ 2) * (1 + y) ^ 2 ≤ D * D := mul_le_mul hD1 hD2 hq.le (by positivity)
    _ = D ^ 2 := by ring

def H (w : P) : ℝ≥0∞ := ENNReal.ofReal (kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))))

/- English proof (translation)
Establish `h1 : Measurable fun w : P => kap iP w` using `(hc.comp (continuous_const.prodMk continuous_id)).measurable`. Establish `h2 : Measurable fun w : P => |w.1.im|` using `(Complex.continuous_im.comp continuous_subtype_val).abs.measurable`. Unfold `H`. Conclude with `ENNReal.measurable_ofReal.comp ((h1.pow_const 2).mul (measurable_const.add (h2.pow_const _)))`.
-/
theorem H_meas (hc : Continuous fun p : P × P => kap p.1 p.2) : Measurable H := by
  have h1 : Measurable fun w : P => kap iP w :=
    (hc.comp (continuous_const.prodMk continuous_id)).measurable
  have h2 : Measurable fun w : P => |w.1.im| :=
    (Complex.continuous_im.comp continuous_subtype_val).abs.measurable
  unfold H
  exact ENNReal.measurable_ofReal.comp ((h1.pow_const 2).mul (measurable_const.add (h2.pow_const _)))

def B (y : ℝ) : ℝ≥0∞ :=
  if 0 < y then ENNReal.ofReal (16 * y ^ 2 / ((1 + y) ^ 2) * (1 + y ^ (-(1 / 2 : ℝ)))) * (ENNReal.ofReal y⁻¹ * A) else 0

/- English proof (translation)
Break down `lt_or_gt_of_ne hy with hn | hp` into its components or cases. Establish `: ∀ x, H (pt x y hy) = 0`. Introduce `x`. Rewrite using `[H, kap_neg _ (by simp [pt, hn])]`. Simplify using the standard rewrite rules.

Simplify using `[this]`. Rewrite using `[B, if_pos hp, ← x_int hp, ← lintegral_const_mul _ (by fun_prop)]`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Rewrite using `[H, ← ENNReal.ofReal_mul (by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Establish `him : |(pt x y hy).1.im| = y` using `by simp [pt, abs_of_pos hp]`. Rewrite using `[him]`. Establish `h` using `kap_sq_le (x := x) hp`. Establish `hp0 : 0 ≤ y ^ (-(1 / 2 : ℝ))` using `Real.rpow_nonneg hp.le _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inner_le (y : ℝ) (hy : y ≠ 0) :
    ∫⁻ x : ℝ, H (pt x y hy) ≤ B y := by
  rcases lt_or_gt_of_ne hy with hn | hp
  · have : ∀ x, H (pt x y hy) = 0 := by
      intro x
      rw [H, kap_neg _ (by simp [pt, hn])]
      simp
    simp [this]
  · rw [B, if_pos hp, ← x_int hp, ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_mono fun x => ?_
    rw [H, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have him : |(pt x y hy).1.im| = y := by simp [pt, abs_of_pos hp]
    rw [him]
    have h := kap_sq_le (x := x) hp
    have hp0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp.le _
    calc kap iP (pt x y hy) ^ 2 * (1 + y ^ (-(1 / 2 : ℝ)))
        ≤ 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ * (1 + y ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring

/- English proof (translation)
Take `⟨hmp, -, hcont⟩` from `h5`. Establish `hHm` using `H_meas hc`. Establish `hBm : Measurable B`. Unfold `B`. Use `Measurable.ite measurableSet_Ioi ?_ measurable_const` and prove the remaining obligations.

Use `fun_prop`. Establish `hs : MeasurableSet {y : ℝ | y ≠ 0}` using `(measurableSet_singleton 0).compl`. Establish `: SigmaFinite (Measure.comap Subtype.val (volume : Measure ℝ) : Measure {y : ℝ // y ≠ 0})`. Use `SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable ?_` and prove the remaining obligations. Use `(inferInstance : SigmaFinite ((volume : Measure ℝ).restrict {y : ℝ | y ≠ 0})) using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `all_goals first | rfl | exact map_comap_subtype_coe hs _`. Establish `e` using `lintegral_prod_symm (μ := volume) (ν := (Measure.comap Subtype.val volume).withDensity fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|)) (fun p : ℝ × {y : ℝ // y ≠ 0} => H (pt p.1 p.2.1 p.2.2)) (hHm.comp hcont.measurable).aemeasurable`. Rewrite using `[← hmp.lintegral_comp hHm]`. Use `lt_of_eq_of_lt e ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `(lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (hBm.comp measurable_subtype_coe)).trans ?_` and prove the remaining obligations. Both sides reduce to the same expression. Use `_ = ∫⁻ y in {y : ℝ | y ≠ 0}, ENNReal.ofReal (1 / |y|) * B y := lintegral_subtype_comap hs (fun y => ENNReal.ofReal (1 / |y|) * B y)`. Use `_ ≤ ∫⁻ y, (Ioi (0 : ℝ)).indicator (fun y => ENNReal.ofReal (16 * F y) * A) y := by`. Use `(setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)` and prove the remaining obligations.

Distinguish the cases in `hy : 0 < y`. Rewrite using `[indicator_of_mem (show y ∈ Ioi 0 from hy), B, if_pos hy, abs_of_pos hy, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `le_of_eq (congrArg (· * A) (congrArg ENNReal.ofReal ?_))` and prove the remaining obligations. Unfold `F`. Clear the denominators using the available nonvanishing facts.

Simplify using `[B, hy]`. Use `_ = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (16 * F y) * A := lintegral_indicator measurableSet_Ioi _`. Use `_ = (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (16 * F y)) * A := lintegral_mul_const _ (by unfold F; fun_prop)`. Use `_ < ∞ := ENNReal.mul_lt_top (F_int.const_mul 16).lintegral_lt_top A_lt`.
-/
theorem H_lt (h5 : UpperHalfPlaneMeasureCoordinates) (hc : Continuous fun p : P × P => kap p.1 p.2) : ∫⁻ w, H w < ∞ := by
  obtain ⟨hmp, -, hcont⟩ := h5
  have hHm := H_meas hc
  have hBm : Measurable B := by
    unfold B
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    fun_prop
  have hs : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have : SigmaFinite (Measure.comap Subtype.val (volume : Measure ℝ) : Measure {y : ℝ // y ≠ 0}) := by
    refine SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable ?_
    convert (inferInstance : SigmaFinite ((volume : Measure ℝ).restrict {y : ℝ | y ≠ 0})) using 1
    all_goals first | rfl | exact map_comap_subtype_coe hs _
  have e := lintegral_prod_symm (μ := volume)
    (ν := (Measure.comap Subtype.val volume).withDensity fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|))
    (fun p : ℝ × {y : ℝ // y ≠ 0} => H (pt p.1 p.2.1 p.2.2)) (hHm.comp hcont.measurable).aemeasurable
  rw [← hmp.lintegral_comp hHm]
  refine lt_of_eq_of_lt e ?_
  calc ∫⁻ y : {y : ℝ // y ≠ 0}, ∫⁻ x : ℝ, H (pt x y.1 y.2) ∂volume
        ∂((Measure.comap Subtype.val volume).withDensity fun y => ENNReal.ofReal (1 / |y.1|))
      ≤ ∫⁻ y : {y : ℝ // y ≠ 0}, B y.1
        ∂((Measure.comap Subtype.val volume).withDensity fun y => ENNReal.ofReal (1 / |y.1|)) :=
        lintegral_mono fun y => inner_le y.1 y.2
    _ = ∫⁻ y : {y : ℝ // y ≠ 0}, ENNReal.ofReal (1 / |y.1|) * B y.1 ∂(Measure.comap Subtype.val volume) := by
        refine (lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (hBm.comp measurable_subtype_coe)).trans ?_
        rfl
    _ = ∫⁻ y in {y : ℝ | y ≠ 0}, ENNReal.ofReal (1 / |y|) * B y :=
        lintegral_subtype_comap hs (fun y => ENNReal.ofReal (1 / |y|) * B y)
    _ ≤ ∫⁻ y, (Ioi (0 : ℝ)).indicator (fun y => ENNReal.ofReal (16 * F y) * A) y := by
        refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
        by_cases hy : 0 < y
        · rw [indicator_of_mem (show y ∈ Ioi 0 from hy), B, if_pos hy, abs_of_pos hy, ← mul_assoc, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          refine le_of_eq (congrArg (· * A) (congrArg ENNReal.ofReal ?_))
          unfold F
          field_simp
        · simp [B, hy]
    _ = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (16 * F y) * A := lintegral_indicator measurableSet_Ioi _
    _ = (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (16 * F y)) * A :=
        lintegral_mul_const _ (by unfold F; fun_prop)
    _ < ∞ := ENNReal.mul_lt_top (F_int.const_mul 16).lintegral_lt_top A_lt

/- English proof (translation)
Establish `hk2 : (2 : ℝ) ≤ (k : ℝ) / 2`. Rewrite using `[le_div_iff₀ (by norm_num)]`. Establish `: (4 : ℝ) ≤ k` using `by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `h0.eq_or_lt with h | h` into its components or cases.

Substitute `h` using the available equality. Rewrite using `[Real.zero_rpow (by linarith)]`. Check the signs of the components of the expression. Use `Real.rpow_le_rpow_of_exponent_ge h h1 hk2` as an intermediate fact. Simplify using `using this`.
-/
theorem rp_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) {k : ℕ} (hk : 4 ≤ k) : t ^ ((k : ℝ) / 2) ≤ t ^ 2 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rcases h0.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (by linarith)]
    positivity
  · have := Real.rpow_le_rpow_of_exponent_ge h h1 hk2
    simpa using this

end UpperTheory.Esk.HyperbolicBallVolume

open UpperTheory.Esk UpperTheory.Esk.HyperbolicBallVolume in
/- English proof (translation)
Introduce `h1a h1b h1c h5 k hk`. Establish `hc` using `h1c.2.2.2.2.1`. Establish `hfin` using `H_lt h5 hc`. Use `⟨(∫⁻ w, H w).toNNReal, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[ENNReal.coe_toNNReal hfin.ne]`.

Take `⟨g, hg0, hg1, hgz⟩` from `h1c.2.2.2.2.2 z`. Substitute `hgz` using the available equality. Establish `hmp` using `(h1a.2.2 g).2`. Establish `him : ∀ w : P, (g • w).1.im = g.val.det * w.1.im`. Introduce `w`.

Establish `hden : den g w.1 = 1` using `by simp [den, hg0, hg1]`. Rewrite using `[coe_smul, im_div, hden, Complex.normSq_one, div_one]`. Establish `hdet : g.val.det ≠ 0` using `g.det_ne_zero`. Establish `hkc : ∀ z : P, Continuous fun w : P => kap z w` using `fun z => hc.comp (continuous_const.prodMk continuous_id)`. Establish `hima : Measurable fun w : P => |w.1.im|` using `(Complex.continuous_im.comp continuous_subtype_val).abs.measurable`.

Establish `hb` using `h1c.1`. Establish `hkinv` using `h1b.2.2.2.1 g iP`. Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Rewrite using `[hkinv w]`. Take `⟨h0, h1, -⟩` from `hb iP w`. Establish `hp0 : 0 ≤ |w.1.im| ^ (-(1 / 2 : ℝ))` using `Real.rpow_nonneg (abs_nonneg _) _`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[hkinv w, him, him]`. Take `⟨h0, h1, -⟩` from `hb iP w`. Establish `e : |g.val.det * iP.1.im| / |g.val.det * w.1.im| = |w.1.im|⁻¹`. Rewrite using `[show iP.1.im = 1 by simp [iP], mul_one, abs_mul, div_mul_eq_div_div, div_self (abs_ne_zero.2 hdet), one_div]`.

Rewrite using `[e, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _)]`. Establish `hp0 : 0 ≤ |w.1.im| ^ (-(1 / 2 : ℝ))` using `Real.rpow_nonneg (abs_nonneg _) _`. Establish `hk'` using `rp_le h0 h1 hk`. Establish `: (-((1 : ℝ) / 2)) = -(1 / 2 : ℝ)` using `rfl`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Esk.hyperbolic_ball_volume_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.B6 := by
  intro h1a h1b h1c h5 k hk
  have hc := h1c.2.2.2.2.1
  have hfin := H_lt h5 hc
  refine ⟨(∫⁻ w, H w).toNNReal, fun z => ?_⟩
  rw [ENNReal.coe_toNNReal hfin.ne]
  obtain ⟨g, hg0, hg1, hgz⟩ := h1c.2.2.2.2.2 z
  subst hgz
  have hmp := (h1a.2.2 g).2
  have him : ∀ w : P, (g • w).1.im = g.val.det * w.1.im := by
    intro w
    have hden : den g w.1 = 1 := by simp [den, hg0, hg1]
    rw [coe_smul, im_div, hden, Complex.normSq_one, div_one]
  have hdet : g.val.det ≠ 0 := g.det_ne_zero
  have hkc : ∀ z : P, Continuous fun w : P => kap z w := fun z =>
    hc.comp (continuous_const.prodMk continuous_id)
  have hima : Measurable fun w : P => |w.1.im| :=
    (Complex.continuous_im.comp continuous_subtype_val).abs.measurable
  have hb := h1c.1
  have hkinv := h1b.2.2.2.1 g iP
  constructor
  · calc ∫⁻ w, ENNReal.ofReal (kap (g • iP) w ^ ((k : ℝ) / 2))
        = ∫⁻ w, ENNReal.ofReal (kap (g • iP) (g • w) ^ ((k : ℝ) / 2)) :=
          (hmp.lintegral_comp (ENNReal.measurable_ofReal.comp ((hkc _).measurable.pow_const _))).symm
      _ ≤ ∫⁻ w, H w := by
          refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
          rw [hkinv w]
          obtain ⟨h0, h1, -⟩ := hb iP w
          have hp0 : 0 ≤ |w.1.im| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
          calc kap iP w ^ ((k : ℝ) / 2) ≤ kap iP w ^ 2 := rp_le h0 h1 hk
            _ ≤ kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))) :=
              le_mul_of_one_le_right (by positivity) (by linarith)
  · calc ∫⁻ w, ENNReal.ofReal (kap (g • iP) w ^ ((k : ℝ) / 2) * (|(g • iP).1.im| / |w.1.im|) ^ ((1 : ℝ) / 2))
        = ∫⁻ w, ENNReal.ofReal (kap (g • iP) (g • w) ^ ((k : ℝ) / 2) *
            (|(g • iP).1.im| / |(g • w).1.im|) ^ ((1 : ℝ) / 2)) :=
          (hmp.lintegral_comp (ENNReal.measurable_ofReal.comp (((hkc _).measurable.pow_const _).mul
            ((measurable_const.div hima).pow_const _)))).symm
      _ ≤ ∫⁻ w, H w := by
          refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
          rw [hkinv w, him, him]
          obtain ⟨h0, h1, -⟩ := hb iP w
          have e : |g.val.det * iP.1.im| / |g.val.det * w.1.im| = |w.1.im|⁻¹ := by
            rw [show iP.1.im = 1 by simp [iP], mul_one, abs_mul, div_mul_eq_div_div, div_self (abs_ne_zero.2 hdet),
              one_div]
          rw [e, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _)]
          have hp0 : 0 ≤ |w.1.im| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
          have hk' := rp_le h0 h1 hk
          have : (-((1 : ℝ) / 2)) = -(1 / 2 : ℝ) := rfl
          calc kap iP w ^ ((k : ℝ) / 2) * |w.1.im| ^ (-((1 : ℝ) / 2))
              ≤ kap iP w ^ 2 * |w.1.im| ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hk' hp0
            _ ≤ kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
