import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoreR
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox

/- English proof (translation)
Use `haveI : ∀ i, SigmaFinite (c i • μ i) := fun i => inferInstance`. Use `Measure.pi_eq fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib, ENNReal.coe_finset_prod]`.
-/
theorem pi_smul_const_family {P : Type} [Fintype P] {X : P → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : P → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  haveI : ∀ i, SigmaFinite (c i • μ i) := fun i => inferInstance
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib, ENNReal.coe_finset_prod]

/- English proof (translation)
Establish `hc : ∀ w, (volume : Measure E).map (fun y => r w • y) = Real.toNNReal ((r w ^ Module.finrank ℝ E)⁻¹) • (volume : Measure E)` using `fun w => by`. Rewrite using `[Measure.map_addHaar_smul _ (hr w).ne', abs_of_pos (inv_pos.mpr (pow_pos (hr w) _))]`. Use extensionality with `s _`. Rewrite using `[Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]`. Use `haveI : ∀ w, SigmaFinite ((volume : Measure E).map (fun y => r w • y)) := fun w => by`.

Rewrite using `[hc w]`. Use `infer_instance`. Establish `hmap` using `Measure.pi_map_pi (μ := fun _ : P => (volume : Measure E)) (f := fun w (y : E) => r w • y) (fun w => (continuous_id.const_smul (r w)).measurable.aemeasurable)`. Use `beta_reduce at hmap`. Rewrite using `[volume_pi, hmap]`.

Simplify using `only [hc]`. Rewrite using `[GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.pi_smul_const_family, ← Real.toNNReal_prod_of_nonneg (fun w _ => (inv_pos.mpr (pow_pos (hr w) (Module.finrank ℝ E))).le)]`. Use extensionality with `s _`. Rewrite using `[Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]`.
-/
theorem map_pi_smul {P : Type} [Fintype P] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] (r : P → ℝ) (hr : ∀ w, 0 < r w) :
    (volume : Measure (P → E)).map (fun x w => r w • x w) =
      ENNReal.ofReal (∏ w, (r w ^ Module.finrank ℝ E)⁻¹) • (volume : Measure (P → E)) := by
  have hc : ∀ w, (volume : Measure E).map (fun y => r w • y) =
      Real.toNNReal ((r w ^ Module.finrank ℝ E)⁻¹) • (volume : Measure E) := fun w => by
    rw [Measure.map_addHaar_smul _ (hr w).ne', abs_of_pos (inv_pos.mpr (pow_pos (hr w) _))]
    ext s _
    rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]
  haveI : ∀ w, SigmaFinite ((volume : Measure E).map (fun y => r w • y)) := fun w => by
    rw [hc w]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : P => (volume : Measure E))
    (f := fun w (y : E) => r w • y)
    (fun w => (continuous_id.const_smul (r w)).measurable.aemeasurable)
  beta_reduce at hmap
  rw [volume_pi, hmap]
  simp only [hc]
  rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.pi_smul_const_family, ← Real.toNNReal_prod_of_nonneg
    (fun w _ => (inv_pos.mpr (pow_pos (hr w) (Module.finrank ℝ E))).le)]
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]

variable {P ι : Type}

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0`. Conclude with `continuous_pi fun w => continuous_const.mul ((continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w)))`.
-/
theorem continuous_qR0 [Fintype ι] (A : P → Matrix ι ι ℝ) : Continuous (qR0 A) := by
  unfold GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0
  exact continuous_pi fun w => continuous_const.mul
    ((continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w)))

/- English proof (translation)
Unfold `gaussR`. Conclude with `Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ => Continuous.dotProduct (continuous_apply w) (Continuous.matrix_mulVec continuous_const (continuous_apply w))))`.
-/
theorem continuous_gaussR [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) :
    Continuous (gaussR Pm) := by
  unfold gaussR
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ =>
    Continuous.dotProduct (continuous_apply w)
      (Continuous.matrix_mulVec continuous_const (continuous_apply w))))

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [boxR, Set.mem_setOf_eq, mem_closedBall_zero_iff]`. Conclude with `(pi_norm_le_iff_of_nonneg zero_le_one).symm`.
-/
theorem boxR_one_eq [Fintype P] [Fintype ι] :
    boxR (fun _ : P => (1 : ℝ)) = Metric.closedBall (0 : P → ι → ℝ) 1 := by
  ext x
  simp only [boxR, Set.mem_setOf_eq, mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).symm

/- English proof (translation)
Establish `hBc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))`. Rewrite using `[GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]`. Conclude with `isCompact_closedBall _ _`. Establish `hBm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))` using `hBc.isClosed.measurableSet`. Establish `hBne : (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)).Nonempty`.

Rewrite using `[GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]`. Conclude with `⟨0, Metric.mem_closedBall_self zero_le_one⟩`. Establish `hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P` using `P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A`. Establish `hKc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A '' (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)))` using `hBc.image hQc`. Take `⟨x₀, -, hx₀⟩` from `hBc.exists_isMinOn hBne (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_gaussR Pm).continuousOn`.

Take `⟨D, hD'⟩` from `hKc.exists_bound_of_continuousOn hDi.continuousOn`. Establish `hm : 0 < GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀` using `Real.exp_pos _`. Use `⟨Real.toNNReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D), fun U hU => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ≤ ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * _`. Establish `hS : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)))` using `(hQc.measurable hU).inter hBm`.

Establish `hK : MeasurableSet (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A '' (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)))` using `hU.inter hKc.isClosed.measurableSet`. Establish `h1 : ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) ≤ ENNReal.ofReal D * volume U`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel₀ hm.ne', ENNReal.ofReal_one, one_mul]`.

Use `_ = ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory …`. Rewrite using `[ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]`. Use `_ ≤ ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal D * volume U) := mul_le_mul_right h1 _`. Use `_ = ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * volume U := by`. Rewrite using `[ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]`.
-/
theorem unit_box_bound [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ)
    (hDi : Continuous Di)
    (hD : ∀ U : Set (P → ℝ), MeasurableSet U →
      ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) :
    ∃ C : ℝ≥0, ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR (fun _ => (1 : ℝ))) ≤
        (C : ℝ≥0∞) * volume U := by
  have hBc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)) := by
    rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]; exact isCompact_closedBall _ _
  have hBm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)) :=
    hBc.isClosed.measurableSet
  have hBne : (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)).Nonempty := by
    rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]; exact ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P := P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A
  have hKc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A '' (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) :=
    hBc.image hQc
  obtain ⟨x₀, -, hx₀⟩ := hBc.exists_isMinOn hBne (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_gaussR Pm).continuousOn
  obtain ⟨D, hD'⟩ := hKc.exists_bound_of_continuousOn hDi.continuousOn
  have hm : 0 < GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀ := Real.exp_pos _
  refine ⟨Real.toNNReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D), fun U hU => ?_⟩
  change _ ≤ ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * _
  have hS : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := (hQc.measurable hU).inter hBm
  have hK : MeasurableSet (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := hU.inter hKc.isClosed.measurableSet
  have h1 : ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ))
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) ≤
      ENNReal.ofReal D * volume U := by
    calc ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ))
          (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))
        = ∫⁻ _ in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x) :=
          setLIntegral_mono' hS fun x hx => ENNReal.ofReal_le_ofReal (isMinOn_iff.mp hx₀ x hx.2)
      _ ≤ ∫⁻ x in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x) :=
          lintegral_mono_set fun x hx => ⟨hx.1, x, hx.2, rfl⟩
      _ = ∫⁻ y in U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)), ENNReal.ofReal (Di y) := hD _ hK
      _ ≤ ∫⁻ _ in U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)), ENNReal.ofReal D :=
          setLIntegral_mono' hK fun y hy =>
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hD' y hy.2))
      _ = ENNReal.ofReal D * volume (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal D * volume U := mul_le_mul_right (measure_mono Set.inter_subset_left) _
  calc (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))
      = ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by
        rw [inv_mul_cancel₀ hm.ne', ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]
    _ ≤ ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal D * volume U) :=
        mul_le_mul_right h1 _
    _ = ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * volume U := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [qR0, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qR0_scale [Fintype ι] (A : P → Matrix ι ι ℝ) (t : P → ℝ) (x : P → ι → ℝ) :
    qR0 A (fun w => t w • x w) = fun w => (t w ^ 2) • qR0 A x w := by
  funext w
  simp only [qR0, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `P ι _ _ A Pm Di hcard hDi hD`. Take `⟨C, hC⟩` from `GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.unit_box_bound A Pm Di hDi hD`. Use `⟨C, fun t ht U hU => ?_⟩` and prove the remaining obligations. Establish `hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P` using `P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A`. Establish `hφm : Measurable (fun (x : P → ι → ℝ) (w : P) => t w • x w)` using `(continuous_pi fun w => (continuous_apply w).const_smul (t w)).measurable`.

Establish `hψm : Measurable (fun (z : P → ℝ) (w : P) => t w ^ 2 • z w)` using `(continuous_pi fun w => (continuous_apply w).const_smul (t w ^ 2)).measurable`. Establish `hBox : IsClosed (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ))` using `by show IsClosed {x : P → ι → ℝ | ∀ w, ‖x w‖ ≤ t w}`. Rewrite using `[Set.setOf_forall]`. Conclude with `isClosed_iInter fun w => isClosed_le (continuous_apply w).norm continuous_const`. Establish `hSm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ)))` using `(hQc.measurable hU).inter hBox.measurableSet`.

Establish `hpre : (fun (x : P → ι → ℝ) (w : P) => t w • x w) ⁻¹' (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) = GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩ Glo …`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_inter_iff, GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.qR0_scale]`. Use `and_congr_right fun _ => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR, Set.mem_setOf_eq]`.

Conclude with `forall_congr' fun w => by`. Rewrite using `[norm_smul, Real.norm_of_nonneg (ht w).le, mul_le_iff_le_one_right (ht w)]`. Establish `hφ` using `GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) (ι → ℝ) t ht`. Establish `hψ` using `GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) ℝ (fun w => t w ^ 2) (fun w => pow_pos (ht w) 2)`. Rewrite `hφ` using `[Module.finrank_fintype_fun_eq_card]`.

Rewrite `hψ` using `[Module.finrank_self]`. Establish `e1 : ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) * (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) = volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) …`. Rewrite using `[← hpre, ← Measure.map_apply hφm hSm, hφ, Measure.smul_apply, smul_eq_mul]`. Establish `e2 : ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * (volume : Measure (P → ℝ)) U = volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U)`. Rewrite using `[← Measure.map_apply hψm hU, hψ, Measure.smul_apply, smul_eq_mul]`.

Establish `hprod : ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) * ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) = 1`. Rewrite using `[← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le), ← Finset.prod_mul_distrib, Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), ENNReal.ofReal_one]`. Establish `hreal : (∏ w, t w ^ Fintype.card ι) * ∏ w, ((t w ^ 2) ^ 1)⁻¹ = ∏ w, t w ^ (Fintype.card ι - 2)`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[pow_one, show t w ^ Fintype.card ι = t w ^ (Fintype.card ι - 2) * t w ^ 2 by`. Rewrite using `[← pow_add, Nat.sub_add_cancel hcard],`. Use the proof step `mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, hprod, one_mul]`.

Use `_ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) * volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by rw [e1]`. Use `_ ≤ ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) * ((C : ℝ≥0∞) * volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U)) := mul_le_mul_right (hC _ (hψm hU)) _`. Use `_ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) * ((C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * volume U)) := by rw [e2]`. Use `_ = (C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) * ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹)) * volume U := by ring`. Use `_ = (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by`.

Rewrite using `[← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le), hreal]`.
-/
theorem image_box_bound : ∀ (P ι : Type) [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ), 2 ≤ Fintype.card ι → Continuous Di → (∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∃ C : ℝ≥0, ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by
  intro P ι _ _ A Pm Di hcard hDi hD
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.unit_box_bound A Pm Di hDi hD
  refine ⟨C, fun t ht U hU => ?_⟩
  have hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P := P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A
  have hφm : Measurable (fun (x : P → ι → ℝ) (w : P) => t w • x w) :=
    (continuous_pi fun w => (continuous_apply w).const_smul (t w)).measurable
  have hψm : Measurable (fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) :=
    (continuous_pi fun w => (continuous_apply w).const_smul (t w ^ 2)).measurable
  have hBox : IsClosed (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ)) := by
    show IsClosed {x : P → ι → ℝ | ∀ w, ‖x w‖ ≤ t w}
    rw [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_le (continuous_apply w).norm continuous_const
  have hSm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ))) :=
    (hQc.measurable hU).inter hBox.measurableSet
  have hpre : (fun (x : P → ι → ℝ) (w : P) => t w • x w) ⁻¹'
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) =
      GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
        GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.qR0_scale]
    refine and_congr_right fun _ => ?_
    simp only [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR, Set.mem_setOf_eq]
    exact forall_congr' fun w => by
      rw [norm_smul, Real.norm_of_nonneg (ht w).le, mul_le_iff_le_one_right (ht w)]
  have hφ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) (ι → ℝ) t ht
  have hψ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) ℝ (fun w => t w ^ 2) (fun w => pow_pos (ht w) 2)
  rw [Module.finrank_fintype_fun_eq_card] at hφ
  rw [Module.finrank_self] at hψ
  have e1 : ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) *
      (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) =
      volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
        GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by
    rw [← hpre, ← Measure.map_apply hφm hSm, hφ, Measure.smul_apply, smul_eq_mul]
  have e2 : ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * (volume : Measure (P → ℝ)) U =
      volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) := by
    rw [← Measure.map_apply hψm hU, hψ, Measure.smul_apply, smul_eq_mul]
  have hprod : ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
      ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le),
      ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), ENNReal.ofReal_one]
  have hreal : (∏ w, t w ^ Fintype.card ι) * ∏ w, ((t w ^ 2) ^ 1)⁻¹ =
      ∏ w, t w ^ (Fintype.card ι - 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [pow_one, show t w ^ Fintype.card ι = t w ^ (Fintype.card ι - 2) * t w ^ 2 by
        rw [← pow_add, Nat.sub_add_cancel hcard],
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), mul_one]
  calc (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t)
      = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) * (ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t)) := by
        rw [← mul_assoc, hprod, one_mul]
    _ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
            GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by rw [e1]
    _ ≤ ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ((C : ℝ≥0∞) * volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U)) :=
        mul_le_mul_right (hC _ (hψm hU)) _
    _ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ((C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * volume U)) := by rw [e2]
    _ = (C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹)) * volume U := by ring
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by
        rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le), hreal]

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
