import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Master
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.IwaInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BochnerOfLintegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import GroundTheory.AutomorphicForms.CuspidalProjection.Global

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Establish `h1 : ∫⁻ p, H p ∂α.prod (β.prod (γ.prod δ)) = 0`. Rewrite using `[lintegral_prod _ hH.aemeasurable, ← h0]`. Use `lintegral_congr fun a => ?_` and prove the remaining obligations. Establish `ha : Measurable fun q : B × C × D => H (a, q)` using `hH.comp measurable_prodMk_left`. Rewrite using `[lintegral_prod _ ha.aemeasurable]`.

Use `lintegral_congr fun b => ?_` and prove the remaining obligations. Establish `hb : Measurable fun q : C × D => H (a, b, q)` using `ha.comp measurable_prodMk_left`. Rewrite using `[lintegral_prod _ hb.aemeasurable]`. Rewrite `h1` using `[lintegral_eq_zero_iff hH]`. Use `filter_upwards [Measure.ae_ae_of_ae_prod h1] with a ha`.

Use `filter_upwards [Measure.ae_ae_of_ae_prod ha] with b hb`. Use `filter_upwards [Measure.ae_ae_of_ae_prod hb] with c hc`. Conclude with `hc`.
-/
private theorem ae4 {A B C D : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (α : Measure A) (β : Measure B) (γ : Measure C) (δ : Measure D) [SFinite β] [SFinite γ] [SFinite δ]
    (H : A × B × C × D → ℝ≥0∞) (hH : Measurable H)
    (h0 : ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, H (a, b, c, d) ∂δ ∂γ ∂β ∂α = 0) :
    ∀ᵐ a ∂α, ∀ᵐ b ∂β, ∀ᵐ c ∂γ, ∀ᵐ d ∂δ, H (a, b, c, d) = 0 := by
  have h1 : ∫⁻ p, H p ∂α.prod (β.prod (γ.prod δ)) = 0 := by
    rw [lintegral_prod _ hH.aemeasurable, ← h0]
    refine lintegral_congr fun a => ?_
    have ha : Measurable fun q : B × C × D => H (a, q) := hH.comp measurable_prodMk_left
    rw [lintegral_prod _ ha.aemeasurable]
    refine lintegral_congr fun b => ?_
    have hb : Measurable fun q : C × D => H (a, b, q) := ha.comp measurable_prodMk_left
    rw [lintegral_prod _ hb.aemeasurable]
  rw [lintegral_eq_zero_iff hH] at h1
  filter_upwards [Measure.ae_ae_of_ae_prod h1] with a ha
  filter_upwards [Measure.ae_ae_of_ae_prod ha] with b hb
  filter_upwards [Measure.ae_ae_of_ae_prod hb] with c hc
  exact hc

/- English proof (translation)
Rewrite using `[integral_prod _ hf]`. Use `integral_eq_zero_of_ae ?_` and prove the remaining obligations. Use `filter_upwards [h, hf.prod_right_ae] with a ha hi`. Conclude with `ha hi`.
-/
private theorem int0 {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    {α : Measure A} {β : Measure B} [SFinite α] [SFinite β] {f : A × B → ℂ} (hf : Integrable f (α.prod β))
    (h : ∀ᵐ a ∂α, Integrable (fun b => f (a, b)) β → ∫ b, f (a, b) ∂β = 0) : ∫ p, f p ∂α.prod β = 0 := by
  rw [integral_prod _ hf]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h, hf.prod_right_ae] with a ha hi
  exact ha hi

/- English proof (translation)
Introduce `K _ _ μ _ F hFc hFP hFB hFD hFN v w hv hw`. Take `⟨-, -, -, hlv, -, -, -, -, -, -, -, hcpt⟩` from `blkLaws (K := K)`. Use `haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.mp (hcpt (2 + 2)).1`. Set `μ₂ : Measure (G1 K 2)` to `Measure.haar`. Set `κ : Measure (KG K (2 + 2))` to `Measure.haar`.

Use `haveI : SecondCountableTopology (G1 K 2) := inferInstance`. Use `haveI : SecondCountableTopology (G1 K (2 + 2)) := inferInstance`. Use `haveI : SecondCountableTopology (KG K (2 + 2)) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : BorelSpace (G1 K 2) := inferInstance`. Use `haveI : BorelSpace (KG K (2 + 2)) := Subtype.borelSpace _`.

Use `haveI : BorelSpace (ℝ × KG K (2 + 2)) := Prod.borelSpace`. Use `haveI : BorelSpace (G1 K 2 × ℝ × KG K (2 + 2)) := Prod.borelSpace`. Use `haveI : BorelSpace (G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2)) := Prod.borelSpace`. Use `haveI : SFinite μ₂ := inferInstance`. Use `haveI : SFinite κ := inferInstance`.

Use `haveI : SFinite (fd μ₂) := inferInstance`. Use `haveI : SFinite ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) := inferInstance`. Use `haveI : SFinite (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))) := Measure.prod.instSFinite`. Use `haveI : SFinite ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))) := inferInstance`. Use `haveI : SFinite (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)))) := Measure.prod.instSFinite`.

Use `haveI : SFinite ((fd μ₂).prod (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))))) := Measure.prod.instSFinite`. Take `⟨⟨c, hc⟩, -⟩` from `unf μ μ₂ κ`. Take `⟨hint, heq, -⟩` from `master μ μ₂ κ c hc F hFc hFP hFB hFD v w hv`. Take `⟨c', hc', hiw⟩` from `iwaInt μ μ₂ κ`. Establish `hm : Measurable (constantTermL2 μ 2 w)` using `(stronglyMeasurable_ctFun 2 (Lp.stronglyMeasurable w)).measurable`.

Establish `h0` using `hiw (fun g => ‖constantTermL2 μ 2 w g‖ₑ) hm.enorm`. Establish `hL : ∫⁻ g, ‖constantTermL2 μ 2 w g‖ₑ ∂μ = 0`. Use `lintegral_eq_zero_of_ae_eq_zero ?_` and prove the remaining obligations. Use `filter_upwards [hw] with g hg`. Simplify using `[hg]`.

Rewrite `h0` using `[hL, eq_comm, mul_eq_zero]`. Establish `h1` using `h0.resolve_left (ENNReal.ofReal_pos.mpr hc').ne'`. Simplify using `only [mul_assoc, CuspidalProjection.constantTermL2_unipotent_mul, lintegral_const] at h1`. Establish `hcont : Continuous fun p : G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) => lv p.1 p.2.1 p.2.2.1 * (p.2.2.2 : G1 K (2 + 2))` using `(hlv.comp (f := fun p : G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) => (p.1, p.2.1, p.2.2.1)) (by fun_prop)).mul (continuous_subtype_val.comp (by fun_prop))`. Establish `h2` using `ae4 μ₂ μ₂ volume κ (fun p : G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) => ‖constantTermL2 μ 2 w (lv p.1 p.2.1 p.2.2.1 * (p.2.2.2 : G1 K (2 + 2)))‖ₑ * (ENNReal.ofReal (Real.exp (-4 * p.2.2.1)) * unipMeasure K (2 + 2) 2 univ)) ((hm.comp hcont.measurable).enorm.mul (Measurable.mul_const (by …`.

Establish `hU : unipMeasure K (2 + 2) 2 univ ≠ 0` using `NeZero.ne _`. Rewrite using `[heq]`. Use `mul_eq_zero_of_right _ ?_` and prove the remaining obligations. Unfold `parM at hint ⊢`. Use `int0 hint ?_` and prove the remaining obligations.

Use `filter_upwards [ae_restrict_of_ae h2] with m₁ h3 hi₁`. Use `int0 hi₁ ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_of_ae h3] with m₂ h4 hi₂`. Use `int0 hi₂ ?_` and prove the remaining obligations. Use `filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h4] with t h5 hi₃`.

Use `int0 hi₃ ?_` and prove the remaining obligations. Use `filter_upwards [h5] with k h6 _`. Establish `h7 : constantTermL2 μ 2 w (lv m₁ m₂ t * (k : G1 K (2 + 2))) = 0`. Break down `mul_eq_zero.mp h6 with h | h` into its components or cases. Conclude with `enorm_eq_zero.mp h`.

Conclude with `absurd h (mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hU)`. Simplify using `only [pt, mul_assoc, hFN]`. Rewrite using `[integral_const_mul]`. Conclude with `mul_eq_zero_of_right _ h7`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.orthCt :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (F : G1 K (2 + 2) → ℂ), Continuous F → (∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) → InBand F → Decays F → (∀ X g, F (nn X * g) = F g) → ∀ v w : L2 μ, Reps μ v (th F) →
      constantTermL2 μ 2 w =ᵐ[μ] 0 → ⟪v, w⟫_ℂ = 0 := by
  intro K _ _ μ _ F hFc hFP hFB hFD hFN v w hv hw
  obtain ⟨-, -, -, hlv, -, -, -, -, -, -, -, hcpt⟩ := blkLaws (K := K)
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.mp (hcpt (2 + 2)).1
  let μ₂ : Measure (G1 K 2) := Measure.haar
  let κ : Measure (KG K (2 + 2)) := Measure.haar
  haveI : SecondCountableTopology (G1 K 2) := inferInstance
  haveI : SecondCountableTopology (G1 K (2 + 2)) := inferInstance
  haveI : SecondCountableTopology (KG K (2 + 2)) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (G1 K 2) := inferInstance
  haveI : BorelSpace (KG K (2 + 2)) := Subtype.borelSpace _
  haveI : BorelSpace (ℝ × KG K (2 + 2)) := Prod.borelSpace
  haveI : BorelSpace (G1 K 2 × ℝ × KG K (2 + 2)) := Prod.borelSpace
  haveI : BorelSpace (G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2)) := Prod.borelSpace
  haveI : SFinite μ₂ := inferInstance
  haveI : SFinite κ := inferInstance
  haveI : SFinite (fd μ₂) := inferInstance
  haveI : SFinite ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) := inferInstance
  haveI : SFinite (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))) :=
    Measure.prod.instSFinite
  haveI : SFinite ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))) := inferInstance
  haveI : SFinite (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod
      (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)))) := Measure.prod.instSFinite
  haveI : SFinite ((fd μ₂).prod (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod
      (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))))) := Measure.prod.instSFinite
  obtain ⟨⟨c, hc⟩, -⟩ := unf μ μ₂ κ
  obtain ⟨hint, heq, -⟩ := master μ μ₂ κ c hc F hFc hFP hFB hFD v w hv
  obtain ⟨c', hc', hiw⟩ := iwaInt μ μ₂ κ
  have hm : Measurable (constantTermL2 μ 2 w) :=
    (stronglyMeasurable_ctFun 2 (Lp.stronglyMeasurable w)).measurable
  have h0 := hiw (fun g => ‖constantTermL2 μ 2 w g‖ₑ) hm.enorm
  have hL : ∫⁻ g, ‖constantTermL2 μ 2 w g‖ₑ ∂μ = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hw] with g hg
    simp [hg]
  rw [hL, eq_comm, mul_eq_zero] at h0
  have h1 := h0.resolve_left (ENNReal.ofReal_pos.mpr hc').ne'
  simp only [mul_assoc, CuspidalProjection.constantTermL2_unipotent_mul, lintegral_const] at h1
  have hcont : Continuous fun p : G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) =>
      lv p.1 p.2.1 p.2.2.1 * (p.2.2.2 : G1 K (2 + 2)) :=
    (hlv.comp (f := fun p : G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) => (p.1, p.2.1, p.2.2.1)) (by fun_prop)).mul
      (continuous_subtype_val.comp (by fun_prop))
  have h2 := ae4 μ₂ μ₂ volume κ (fun p : G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) =>
      ‖constantTermL2 μ 2 w (lv p.1 p.2.1 p.2.2.1 * (p.2.2.2 : G1 K (2 + 2)))‖ₑ *
        (ENNReal.ofReal (Real.exp (-4 * p.2.2.1)) * unipMeasure K (2 + 2) 2 univ))
    ((hm.comp hcont.measurable).enorm.mul (Measurable.mul_const (by fun_prop) _)) h1
  have hU : unipMeasure K (2 + 2) 2 univ ≠ 0 := NeZero.ne _
  rw [heq]
  refine mul_eq_zero_of_right _ ?_
  unfold parM at hint ⊢
  refine int0 hint ?_
  filter_upwards [ae_restrict_of_ae h2] with m₁ h3 hi₁
  refine int0 hi₁ ?_
  filter_upwards [ae_restrict_of_ae h3] with m₂ h4 hi₂
  refine int0 hi₂ ?_
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h4] with t h5 hi₃
  refine int0 hi₃ ?_
  filter_upwards [h5] with k h6 _
  have h7 : constantTermL2 μ 2 w (lv m₁ m₂ t * (k : G1 K (2 + 2))) = 0 := by
    rcases mul_eq_zero.mp h6 with h | h
    · exact enorm_eq_zero.mp h
    · exact absurd h (mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hU)
  simp only [pt, mul_assoc, hFN]
  rw [integral_const_mul]
  exact mul_eq_zero_of_right _ h7
