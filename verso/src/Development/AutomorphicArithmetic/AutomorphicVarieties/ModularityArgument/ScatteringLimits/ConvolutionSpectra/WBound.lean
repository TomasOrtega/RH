import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

/- English proof (translation)
Establish `e1 : ∀ x : ℝ, ENNReal.ofReal (Real.exp (2 * x)) = ∫⁻ a in Iio x, ENNReal.ofReal (2 * Real.exp (2 * a))` using `fun x => by`. Rewrite using `[setLIntegral_congr Iio_ae_eq_Iic, ← ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_mul_Iic two_pos x).const_mul 2) (Eventually.of_forall fun _ => by positivity), integral_const_mul, integral_exp_mul_Iic two_pos]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `m : Measurable fun z : ℝ × ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) z` using `Measurable.indicator (by fun_prop) (measurableSet_lt measurable_snd measurable_fst)`.

Use `lintegral_lintegral_swap (μ := volume) (ν := volume) (f := fun x a : ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) (x, a)) m.aemeasurable` as an intermediate fact. Use `(lintegral_congr fun x => ?_).trans (this.trans (lintegral_congr fun a => ?_))` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_mul (Real.exp_pos _).le, e1, ← lintegral_mul_const _ (by fun_prop), ← lintegral_indicator measurableSet_Iio]`. Both sides reduce to the same expression. Rewrite using `[← lintegral_const_mul _ (by fun_prop), ← lintegral_indicator measurableSet_Ioi]`.

Both sides reduce to the same expression.
-/
private theorem layer (f : ℝ → ℝ) (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (2 * x) * f x) =
      ∫⁻ a, ENNReal.ofReal (2 * Real.exp (2 * a)) * ∫⁻ x in Ioi a, ENNReal.ofReal (f x) := by
  have e1 : ∀ x : ℝ, ENNReal.ofReal (Real.exp (2 * x)) = ∫⁻ a in Iio x, ENNReal.ofReal (2 * Real.exp (2 * a)) := fun x => by
    rw [setLIntegral_congr Iio_ae_eq_Iic, ← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_exp_mul_Iic two_pos x).const_mul 2) (Eventually.of_forall fun _ => by positivity), integral_const_mul,
      integral_exp_mul_Iic two_pos]
    congr 1; ring
  have m : Measurable fun z : ℝ × ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator
      (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) z :=
    Measurable.indicator (by fun_prop) (measurableSet_lt measurable_snd measurable_fst)
  have := lintegral_lintegral_swap (μ := volume) (ν := volume) (f := fun x a : ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator
      (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) (x, a)) m.aemeasurable
  refine (lintegral_congr fun x => ?_).trans (this.trans (lintegral_congr fun a => ?_))
  · rw [ENNReal.ofReal_mul (Real.exp_pos _).le, e1, ← lintegral_mul_const _ (by fun_prop), ← lintegral_indicator measurableSet_Iio]
    rfl
  · rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_indicator measurableSet_Ioi]
    rfl

/- English proof (translation)
Introduce `V _ _ _ _ W _ _ _ _ g p c Q h ⟨hp1, hp2⟩`. Establish `ig : Integrable fun x => ‖g x‖ ^ 2` using `(memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)`. Establish `ip : Integrable fun x => ‖p x‖ ^ 2` using `(memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable p)).1 (Lp.memLp p)`. Establish `mg : Measurable fun x => ‖g x‖ ^ 2` using `(Lp.stronglyMeasurable g).norm.measurable.pow_const 2`. Establish `mp : Measurable fun x => ‖p x‖ ^ 2` using `(Lp.stronglyMeasurable p).norm.measurable.pow_const 2`.

Establish `ip' : Integrable fun x => ‖p (c - x)‖ ^ 2` using `ip.comp_sub_left c`. Establish `h1 : ∀ a, ∫⁻ x in Ioi a, ENNReal.ofReal (‖g x‖ ^ 2) ≤ ∫⁻ x in Ioi a, ENNReal.ofReal (‖p (c - x)‖ ^ 2)` using `fun a => by`. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal ig.integrableOn (Eventually.of_forall fun _ => by positivity), ← ofReal_integral_eq_lintegral_ofReal ip'.integrableOn (Eventually.of_forall fun _ => by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `e : ∫ x in Ioi a, ‖p (c - x)‖ ^ 2 = ∫ x in Iic (c - a), ‖p x‖ ^ 2`.

Rewrite using `[← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Iic, ← integral_sub_left_eq_self _ volume c]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `b : x ≤ c - a`. Simplify using `[indicator, b, show a ≤ c - x by linarith]`. Simplify using `[indicator, b, show ¬ a ≤ c - x from fun k => b (by linarith)]`.

Rewrite using `[e, ← (cutLaws (V := V) _ univ measurableSet_Ioi .univ).2.2.2.2.2.2.2.2, ← (cutLaws (V := W) _ univ measurableSet_Iic .univ).2.2.2.2.2.2.2.2]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (h a) 2`. Establish `i2 : Integrable fun x => Real.exp (2 * x) * ‖p (c - x)‖ ^ 2`. Use `((hp1.comp_sub_left c).const_mul (Real.exp (2 * c))).congr (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← mul_assoc, ← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `v2 : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 ≤ (Real.exp c * Q) ^ 2`. Establish `e : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 = Real.exp (2 * c) * ∫ x, Real.exp (-2 * x) * ‖p x‖ ^ 2`. Rewrite using `[← integral_sub_left_eq_self (fun x => Real.exp (-2 * x) * ‖p x‖ ^ 2) volume c, ← integral_const_mul]`.

Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← mul_assoc, ← Real.exp_add]`. Put the polynomial expressions in normal form. Rewrite using `[e, mul_pow, ← Real.exp_nat_mul]`.

Conclude with `mul_le_mul_of_nonneg_left hp2 (Real.exp_pos _).le`. Establish `mp' : Measurable fun x => ‖p (c - x)‖ ^ 2` using `mp.comp (measurable_const.sub measurable_id)`. Establish `h2 : ∫⁻ x, ENNReal.ofReal (Real.exp (2 * x) * ‖g x‖ ^ 2) ≤ ENNReal.ofReal ((Real.exp c * Q) ^ 2)`. Use `le_trans ?_ (ENNReal.ofReal_le_ofReal v2)` and prove the remaining obligations. Rewrite using `[ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun _ => by positivity), layer _ mg, layer _ mp']`.

Conclude with `lintegral_mono fun a => mul_le_mul' le_rfl (h1 a)`. Establish `m2 : Measurable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2` using `(by fun_prop : Measurable fun x : ℝ => Real.exp (2 * x)).mul mg`. Establish `i3 : Integrable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2` using `⟨m2.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)).2 (h2.trans_lt ENNReal.ofReal_lt_top)⟩`. Use `⟨i3, ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[← ofReal_integral_eq_lintegral_ofReal i3 (Eventually.of_forall fun _ => by positivity)]`.

Conclude with `(ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2`.
-/
theorem UpperTheory.V.Z.IntegralApplyAeEq.wBound :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (g : L V) (p : L W) (c Q : ℝ), (∀ a : ℝ, ‖cut V (Ioi a) g‖ ≤ ‖cut W (Iic (c - a)) p‖) → WLe (-2) p Q → WLe 2 g (Real.exp c * Q) := by
  intro V _ _ _ _ W _ _ _ _ g p c Q h ⟨hp1, hp2⟩
  have ig : Integrable fun x => ‖g x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have ip : Integrable fun x => ‖p x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable p)).1 (Lp.memLp p)
  have mg : Measurable fun x => ‖g x‖ ^ 2 := (Lp.stronglyMeasurable g).norm.measurable.pow_const 2
  have mp : Measurable fun x => ‖p x‖ ^ 2 := (Lp.stronglyMeasurable p).norm.measurable.pow_const 2
  have ip' : Integrable fun x => ‖p (c - x)‖ ^ 2 := ip.comp_sub_left c
  have h1 : ∀ a, ∫⁻ x in Ioi a, ENNReal.ofReal (‖g x‖ ^ 2) ≤ ∫⁻ x in Ioi a, ENNReal.ofReal (‖p (c - x)‖ ^ 2) := fun a => by
    rw [← ofReal_integral_eq_lintegral_ofReal ig.integrableOn (Eventually.of_forall fun _ => by positivity),
      ← ofReal_integral_eq_lintegral_ofReal ip'.integrableOn (Eventually.of_forall fun _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∫ x in Ioi a, ‖p (c - x)‖ ^ 2 = ∫ x in Iic (c - a), ‖p x‖ ^ 2 := by
      rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Iic,
        ← integral_sub_left_eq_self _ volume c]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases b : x ≤ c - a
      · simp [indicator, b, show a ≤ c - x by linarith]
      · simp [indicator, b, show ¬ a ≤ c - x from fun k => b (by linarith)]
    rw [e, ← (cutLaws (V := V) _ univ measurableSet_Ioi .univ).2.2.2.2.2.2.2.2,
      ← (cutLaws (V := W) _ univ measurableSet_Iic .univ).2.2.2.2.2.2.2.2]
    exact pow_le_pow_left₀ (norm_nonneg _) (h a) 2
  have i2 : Integrable fun x => Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 := by
    refine ((hp1.comp_sub_left c).const_mul (Real.exp (2 * c))).congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]; ring_nf
  have v2 : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 ≤ (Real.exp c * Q) ^ 2 := by
    have e : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 = Real.exp (2 * c) * ∫ x, Real.exp (-2 * x) * ‖p x‖ ^ 2 := by
      rw [← integral_sub_left_eq_self (fun x => Real.exp (-2 * x) * ‖p x‖ ^ 2) volume c, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_assoc, ← Real.exp_add]; ring_nf
    rw [e, mul_pow, ← Real.exp_nat_mul]
    exact mul_le_mul_of_nonneg_left hp2 (Real.exp_pos _).le
  have mp' : Measurable fun x => ‖p (c - x)‖ ^ 2 := mp.comp (measurable_const.sub measurable_id)
  have h2 : ∫⁻ x, ENNReal.ofReal (Real.exp (2 * x) * ‖g x‖ ^ 2) ≤ ENNReal.ofReal ((Real.exp c * Q) ^ 2) := by
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal v2)
    rw [ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun _ => by positivity), layer _ mg, layer _ mp']
    exact lintegral_mono fun a => mul_le_mul' le_rfl (h1 a)
  have m2 : Measurable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2 := (by fun_prop : Measurable fun x : ℝ => Real.exp (2 * x)).mul mg
  have i3 : Integrable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2 :=
    ⟨m2.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)).2
      (h2.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨i3, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal i3 (Eventually.of_forall fun _ => by positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
