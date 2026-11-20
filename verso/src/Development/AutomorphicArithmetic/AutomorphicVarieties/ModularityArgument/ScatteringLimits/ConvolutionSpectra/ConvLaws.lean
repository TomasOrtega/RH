import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

/- English proof (translation)
Take `⟨R, hR⟩` from `h.isCompact.isBounded.exists_norm_le`. Use `⟨|R|, abs_nonneg _, fun t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩` and prove the remaining obligations. Conclude with `absurd ((hR t hm).trans (le_abs_self R)) (not_le.2 ht)`.
-/
private theorem ker_bd {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {κ : ℝ → V →L[ℂ] W} (h : HasCompactSupport κ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.exists_norm_le
  refine ⟨|R|, abs_nonneg _, fun t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  exact absurd ((hR t hm).trans (le_abs_self R)) (not_le.2 ht)

/- English proof (translation)
Introduce `V _ _ _ _ W _ _ _ _ κ hk`. Establish `q : ∀ x : ℝ, Measure.QuasiMeasurePreserving (fun t : ℝ => x + t) volume volume` using `fun x => (measurePreserving_add_left volume x).quasiMeasurePreserving`. Use `⟨fun a => ?_, fun ρ T hρ => ?_, fun p ⟨ρ, hp⟩ => ?_⟩` and prove the remaining obligations. Use `ext1 u`. Use `Lp.ext ?_` and prove the remaining obligations.

Use `filter_upwards [(convSpec κ hk (sh V a u)).1, sh_ae W a (conv κ u), (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (convSpec κ hk u).1] with x h1 h2 h3`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[h1, h2, h3]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [(q x).ae (sh_ae V a u)] with t ht`.

Rewrite using `[ht, add_right_comm]`. Use `ext1 u`. Establish `c1` using `(cutLaws (V := W) (Iic (T + ρ)) (Ioi (T + ρ)) measurableSet_Iic measurableSet_Ioi).2.2.2.2.2.2.2.1`. Establish `c2` using `cutLaws (V := W) (Ioi (T + ρ)) (Iic (T + ρ)) measurableSet_Ioi measurableSet_Iic`. Establish `c3` using `cutLaws (V := V) (Iic T) (Iic T) measurableSet_Iic measurableSet_Iic`.

Establish `h0` using `(c3.2.2.2.2.2.2.2.1 (cut V (Iic T) u)).1 (by`. Use `DFunLike.congr_fun c3.1 u` as an intermediate fact. Rewrite using `[inter_self] at this)` and apply the resulting hypothesis. Establish `h1 : cut W (Iic (T + ρ)) (conv κ (cut V (Iic T) u)) = conv κ (cut V (Iic T) u)`. Use `(c1 _).2 ?_` and prove the remaining obligations.

Use `filter_upwards [(convSpec κ hk (cut V (Iic T) u)).1] with x hx hx'`. Rewrite using `[hx]`. Use `integral_eq_zero_of_ae ?_` and prove the remaining obligations. Use `filter_upwards [(q x).ae h0] with t ht`. Distinguish the cases in `h : ρ < |t|`.

Simplify using `[hρ t h]`. Establish `h2` using `(abs_le.1 (not_lt.1 h)).1`. Rewrite using `[ht (by simp only [mem_Iic, not_le] at hx' ⊢; linarith), map_zero]; rfl`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]`. Rewrite using `[← h1]`.

Use `DFunLike.congr_fun c2.1 (conv κ (cut V (Iic T) u))` as an intermediate fact. Rewrite `this` using `[Ioi_inter_Iic, Ioc_self, c2.2.2.2.2.1]`. Conclude with `this`. Take `⟨R, -, hR⟩` from `ker_bd hk.2`. Establish `h0` using `((cutLaws (V := V) (Icc (-ρ) ρ) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 p).1 hp`.

Establish `hpi : Integrable (p : ℝ → V)`. Establish `h1 : IntegrableOn (p : ℝ → V) (Icc (-ρ) ρ)` using `integrableOn_Lp_of_measure_ne_top p (by norm_num) measure_Icc_lt_top.ne`. Use `((integrable_indicator_iff measurableSet_Icc).2 h1).congr ?_` and prove the remaining obligations. Use `filter_upwards [h0] with x hx`. Distinguish the cases in `h : x ∈ Icc (-ρ) ρ`.

Rewrite using `[indicator_of_mem h]`. Rewrite using `[indicator_of_notMem h, hx h]`. Use `⟨⟨ρ + R, ((cutLaws (V := W) (Icc (-(ρ + R)) (ρ + R)) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 _).2 ?_⟩, ?_⟩` and prove the remaining obligations. Use `filter_upwards [(convSpec κ hk p).1] with x hx hx'`. Rewrite using `[hx]`.

Use `integral_eq_zero_of_ae ?_` and prove the remaining obligations. Use `filter_upwards [(q x).ae h0] with t ht`. Distinguish the cases in `h : R < |t|`. Simplify using `[hR t h]`. Take `⟨h2, h3⟩` from `abs_le.1 (not_lt.1 h)`.

Rewrite using `[ht fun hm => hx' ⟨by linarith [hm.1], by linarith [hm.2]⟩, map_zero]; rfl`. Establish `hk1 : Integrable κ` using `hk.1.integrable_of_hasCompactSupport hk.2`. Establish `hm : AEStronglyMeasurable (fun z : ℝ × ℝ => κ z.1 ((p : ℝ → V) (z.2 + z.1))) (volume.prod volume)` using `(ContinuousLinearMap.apply ℂ W).flip.aestronglyMeasurable_comp₂ (hk.1.comp continuous_fst).aestronglyMeasurable ((Lp.stronglyMeasurable p).comp_measurable (measurable_snd.add measurable_fst)).aestronglyMeasurable`. Establish `hI : Integrable (fun z : ℝ × ℝ => κ z.1 ((p : ℝ → V) (z.2 + z.1))) (volume.prod volume)`. Use `(integrable_prod_iff hm).2 ⟨Eventually.of_forall fun t => (κ t).integrable_comp (hpi.comp_add_right t), ?_⟩` and prove the remaining obligations.

Use `(hk1.norm.mul_const (∫ x, ‖p x‖)).mono' hm.norm.integral_prod_right' (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← integral_add_right_eq_self (fun x => ‖p x‖) t, ← integral_const_mul]`. Conclude with `integral_mono ((κ t).integrable_comp (hpi.comp_add_right t)).norm ((hpi.comp_add_right t).norm.const_mul _) fun x => (κ t).le_opNorm _`. Rewrite using `[integral_congr_ae (convSpec κ hk p).1, ← integral_integral_swap (f := fun t x => κ t ((p : ℝ → V) (x + t))) hI, symb]`. Simplify using `only [zero_mul, Complex.exp_zero, one_smul]`.

Rewrite using `[ContinuousLinearMap.integral_apply hk1]`. Use `integral_congr_ae (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[(κ t).integral_comp_comm (hpi.comp_add_right t), integral_add_right_eq_self]`.
-/
theorem UpperTheory.V.Z.IntegralApplyAeEq.convLaws :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → (∀ a : ℝ, conv κ ∘L sh V a = sh W a ∘L conv κ) ∧
      (∀ ρ T : ℝ, (∀ t, ρ < |t| → κ t = 0) → cut W (Ioi (T + ρ)) ∘L conv κ ∘L cut V (Iic T) = 0) ∧
      ∀ p : L V, Bdd p → Bdd (conv κ p) ∧ ∫ x, conv κ p x = symb κ 0 (∫ x, p x) := by
  intro V _ _ _ _ W _ _ _ _ κ hk
  have q : ∀ x : ℝ, Measure.QuasiMeasurePreserving (fun t : ℝ => x + t) volume volume :=
    fun x => (measurePreserving_add_left volume x).quasiMeasurePreserving
  refine ⟨fun a => ?_, fun ρ T hρ => ?_, fun p ⟨ρ, hp⟩ => ?_⟩
  · ext1 u
    refine Lp.ext ?_
    filter_upwards [(convSpec κ hk (sh V a u)).1, sh_ae W a (conv κ u),
      (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (convSpec κ hk u).1] with x h1 h2 h3
    simp only [ContinuousLinearMap.comp_apply]
    rw [h1, h2, h3]
    refine integral_congr_ae ?_
    filter_upwards [(q x).ae (sh_ae V a u)] with t ht
    rw [ht, add_right_comm]
  · ext1 u
    have c1 := (cutLaws (V := W) (Iic (T + ρ)) (Ioi (T + ρ)) measurableSet_Iic measurableSet_Ioi).2.2.2.2.2.2.2.1
    have c2 := cutLaws (V := W) (Ioi (T + ρ)) (Iic (T + ρ)) measurableSet_Ioi measurableSet_Iic
    have c3 := cutLaws (V := V) (Iic T) (Iic T) measurableSet_Iic measurableSet_Iic
    have h0 := (c3.2.2.2.2.2.2.2.1 (cut V (Iic T) u)).1 (by
      have := DFunLike.congr_fun c3.1 u
      rwa [inter_self] at this)
    have h1 : cut W (Iic (T + ρ)) (conv κ (cut V (Iic T) u)) = conv κ (cut V (Iic T) u) := by
      refine (c1 _).2 ?_
      filter_upwards [(convSpec κ hk (cut V (Iic T) u)).1] with x hx hx'
      rw [hx]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [(q x).ae h0] with t ht
      by_cases h : ρ < |t|
      · simp [hρ t h]
      · have h2 := (abs_le.1 (not_lt.1 h)).1
        rw [ht (by simp only [mem_Iic, not_le] at hx' ⊢; linarith), map_zero]; rfl
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    rw [← h1]
    have := DFunLike.congr_fun c2.1 (conv κ (cut V (Iic T) u))
    rw [Ioi_inter_Iic, Ioc_self, c2.2.2.2.2.1] at this
    exact this
  · obtain ⟨R, -, hR⟩ := ker_bd hk.2
    have h0 := ((cutLaws (V := V) (Icc (-ρ) ρ) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 p).1 hp
    have hpi : Integrable (p : ℝ → V) := by
      have h1 : IntegrableOn (p : ℝ → V) (Icc (-ρ) ρ) := integrableOn_Lp_of_measure_ne_top p (by norm_num) measure_Icc_lt_top.ne
      refine ((integrable_indicator_iff measurableSet_Icc).2 h1).congr ?_
      filter_upwards [h0] with x hx
      by_cases h : x ∈ Icc (-ρ) ρ
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h, hx h]
    refine ⟨⟨ρ + R, ((cutLaws (V := W) (Icc (-(ρ + R)) (ρ + R)) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 _).2 ?_⟩, ?_⟩
    · filter_upwards [(convSpec κ hk p).1] with x hx hx'
      rw [hx]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [(q x).ae h0] with t ht
      by_cases h : R < |t|
      · simp [hR t h]
      · obtain ⟨h2, h3⟩ := abs_le.1 (not_lt.1 h)
        rw [ht fun hm => hx' ⟨by linarith [hm.1], by linarith [hm.2]⟩, map_zero]; rfl
    · have hk1 : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
      have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => κ z.1 ((p : ℝ → V) (z.2 + z.1))) (volume.prod volume) :=
        (ContinuousLinearMap.apply ℂ W).flip.aestronglyMeasurable_comp₂ (hk.1.comp continuous_fst).aestronglyMeasurable
          ((Lp.stronglyMeasurable p).comp_measurable (measurable_snd.add measurable_fst)).aestronglyMeasurable
      have hI : Integrable (fun z : ℝ × ℝ => κ z.1 ((p : ℝ → V) (z.2 + z.1))) (volume.prod volume) := by
        refine (integrable_prod_iff hm).2 ⟨Eventually.of_forall fun t => (κ t).integrable_comp (hpi.comp_add_right t), ?_⟩
        refine (hk1.norm.mul_const (∫ x, ‖p x‖)).mono' hm.norm.integral_prod_right' (Eventually.of_forall fun t => ?_)
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← integral_add_right_eq_self (fun x => ‖p x‖) t,
          ← integral_const_mul]
        exact integral_mono ((κ t).integrable_comp (hpi.comp_add_right t)).norm ((hpi.comp_add_right t).norm.const_mul _)
          fun x => (κ t).le_opNorm _
      rw [integral_congr_ae (convSpec κ hk p).1, ← integral_integral_swap (f := fun t x => κ t ((p : ℝ → V) (x + t))) hI, symb]
      simp only [zero_mul, Complex.exp_zero, one_smul]
      rw [ContinuousLinearMap.integral_apply hk1]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      rw [(κ t).integral_comp_comm (hpi.comp_add_right t), integral_add_right_eq_self]
