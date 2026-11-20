import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorHomeo
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorLeft

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _`. Take `⟨hcl, e, he⟩` from `M.borHomeo F`. Establish `hcont : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2` using `(M.continuous_ab.inv₀ fun a => (M.ab_pos a).ne').pow 2`. Establish `hwm : Measurable (M.wt : IdeleGroup F → ℝ≥0∞)` using `M.measurable_wt`. Establish `hw0 : ∀ a : IdeleGroup F, M.wt a ≠ 0` using `fun a => by`.

Establish `: 0 < (ab a)⁻¹ ^ 2` using `pow_pos (inv_pos.2 (M.ab_pos a)) 2`. Conclude with `(ENNReal.ofReal_pos.2 this).ne'`. Use `set ν : Measure (IdeleGroup F) := (ideleMeasure F).withDensity M.wt with hν`. Use `haveI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hcont`. Use `haveI : ν.IsOpenPosMeasure := (withDensity_absolutelyContinuous' hwm.aemeasurable (ae_of_all _ hw0)).isOpenPosMeasure`.

Use `haveI : SFinite ν := by rw [hν]; infer_instance`. Use `set ρ : Measure (IdeleGroup F × A F) := ν.prod (adeleMeasure F) with hρ`. Establish `hint : ∀ f : G1 F → ℝ≥0∞, Measurable f → ∫⁻ s, f s ∂(ρ.map e) = ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F)`. Introduce `f hf`. Establish `hc : Continuous fun p : IdeleGroup F × A F => nU p.2 * mD p.1` using `(M.continuous_nU.comp continuous_snd).mul (M.continuous_mD.comp continuous_fst)`.

Establish `hfm : Measurable fun p : IdeleGroup F × A F => f (nU p.2 * mD p.1)` using `hf.comp hc.measurable`. Rewrite using `[show ∫⁻ s, f s ∂(ρ.map e) = ∫⁻ p, f (e p) ∂ρ from lintegral_map (f := fun s : M.Bor F => f s) (hf.comp measurable_subtype_coe) e.continuous.measurable]`. Simplify using `only [he]`. Rewrite using `[hρ, lintegral_prod _ hfm.aemeasurable, hν, lintegral_withDensity_eq_lintegral_mul _ hwm hfm.lintegral_prod_right']`. Use `lintegral_congr fun a => ?_` and prove the remaining obligations.

Establish `hne : M.wt a ≠ ⊤` using `ENNReal.ofReal_ne_top`. Rewrite using `[Pi.mul_apply, lintegral_mul_const' _ _ hne, mul_comm]`. Use `⟨ρ.map e, ?_, hint⟩` and prove the remaining obligations. Use `haveI : IsFiniteMeasureOnCompacts (ρ.map e) := ⟨fun K hK => by`. Rewrite using `[e.measurableEmbedding.map_apply]`.

Conclude with `((e.isCompact_preimage).2 hK).measure_lt_top⟩`. Use `haveI : (ρ.map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective`. Use `haveI : (ρ.map e).IsMulLeftInvariant := ⟨fun g => by`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply (measurable_const_mul g) hs]`.

Establish `hS : MeasurableSet (Subtype.val '' s : Set (G1 F))` using `hcl.measurableSet.subtype_image hs`. Use `set f : G1 F → ℝ≥0∞ := (Subtype.val '' s : Set (G1 F)).indicator 1 with hfdef`. Establish `hf : Measurable f` using `measurable_one.indicator hS`. Establish `hval : ∀ x : M.Bor F, f x = s.indicator 1 x` using `fun x => by`. Distinguish the cases in `hx : x ∈ s`.

Rewrite using `[Set.indicator_of_mem hx, hfdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hx, hfdef, Set.indicator_of_notMem]`. Introduce and unpack `⟨y, hy, hyx⟩`. Conclude with `hx (Subtype.ext hyx ▸ hy)`.

Establish `h1 : (ρ.map e) s = ∫⁻ x, f x ∂(ρ.map e)`. Simplify using `only [hval]`. Rewrite using `[lintegral_indicator_one hs]`. Establish `h2 : (ρ.map e) ((fun x => g * x) ⁻¹' s) = ∫⁻ x, (fun y => f (g.1 * y)) x ∂(ρ.map e)`. Establish `hs' : MeasurableSet ((fun x => g * x) ⁻¹' s)` using `measurable_const_mul g hs`.

Rewrite using `[← lintegral_indicator_one hs']`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Use `hval (g * x)` as an intermediate fact. Simplify `this.symm` using `[Set.indicator]`. Take `⟨p, rfl⟩` from `e.surjective g`.

Rewrite using `[h1, h2, hint (fun y => f ((e p : G1 F) * y)) (hf.comp (measurable_const_mul _)), hint f hf]`. Simplify using `only [he]`. Conclude with `M.borLeft F f hf p.2 p.1⟩`. Conclude with `{}`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.borHaar :
    ∀ (F : Type) [Field F] [NumberField F], ∃ μS : Measure (M.Bor F), μS.IsHaarMeasure ∧ ∀ (f : G1 F → ℝ≥0∞), Measurable f → ∫⁻ s, f s ∂μS = ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
  intro F _ _
  obtain ⟨hcl, e, he⟩ := M.borHomeo F
  have hcont : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 :=
    (M.continuous_ab.inv₀ fun a => (M.ab_pos a).ne').pow 2
  have hwm : Measurable (M.wt : IdeleGroup F → ℝ≥0∞) := M.measurable_wt
  have hw0 : ∀ a : IdeleGroup F, M.wt a ≠ 0 := fun a => by
    have : 0 < (ab a)⁻¹ ^ 2 := pow_pos (inv_pos.2 (M.ab_pos a)) 2
    exact (ENNReal.ofReal_pos.2 this).ne'
  set ν : Measure (IdeleGroup F) := (ideleMeasure F).withDensity M.wt with hν
  haveI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hcont
  haveI : ν.IsOpenPosMeasure :=
    (withDensity_absolutelyContinuous' hwm.aemeasurable (ae_of_all _ hw0)).isOpenPosMeasure
  haveI : SFinite ν := by rw [hν]; infer_instance
  set ρ : Measure (IdeleGroup F × A F) := ν.prod (adeleMeasure F) with hρ
  have hint : ∀ f : G1 F → ℝ≥0∞, Measurable f → ∫⁻ s, f s ∂(ρ.map e) =
      ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
    intro f hf
    have hc : Continuous fun p : IdeleGroup F × A F => nU p.2 * mD p.1 :=
      (M.continuous_nU.comp continuous_snd).mul (M.continuous_mD.comp continuous_fst)
    have hfm : Measurable fun p : IdeleGroup F × A F => f (nU p.2 * mD p.1) := hf.comp hc.measurable
    rw [show ∫⁻ s, f s ∂(ρ.map e) = ∫⁻ p, f (e p) ∂ρ from
      lintegral_map (f := fun s : M.Bor F => f s) (hf.comp measurable_subtype_coe) e.continuous.measurable]
    simp only [he]
    rw [hρ, lintegral_prod _ hfm.aemeasurable, hν,
      lintegral_withDensity_eq_lintegral_mul _ hwm hfm.lintegral_prod_right']
    refine lintegral_congr fun a => ?_
    have hne : M.wt a ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [Pi.mul_apply, lintegral_mul_const' _ _ hne, mul_comm]
  refine ⟨ρ.map e, ?_, hint⟩
  haveI : IsFiniteMeasureOnCompacts (ρ.map e) := ⟨fun K hK => by
    rw [e.measurableEmbedding.map_apply]
    exact ((e.isCompact_preimage).2 hK).measure_lt_top⟩
  haveI : (ρ.map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  haveI : (ρ.map e).IsMulLeftInvariant := ⟨fun g => by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs]
    have hS : MeasurableSet (Subtype.val '' s : Set (G1 F)) := hcl.measurableSet.subtype_image hs
    set f : G1 F → ℝ≥0∞ := (Subtype.val '' s : Set (G1 F)).indicator 1 with hfdef
    have hf : Measurable f := measurable_one.indicator hS
    have hval : ∀ x : M.Bor F, f x = s.indicator 1 x := fun x => by
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, hfdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]; rfl
      · rw [Set.indicator_of_notMem hx, hfdef, Set.indicator_of_notMem]
        rintro ⟨y, hy, hyx⟩
        exact hx (Subtype.ext hyx ▸ hy)
    have h1 : (ρ.map e) s = ∫⁻ x, f x ∂(ρ.map e) := by
      simp only [hval]; rw [lintegral_indicator_one hs]
    have h2 : (ρ.map e) ((fun x => g * x) ⁻¹' s) = ∫⁻ x, (fun y => f (g.1 * y)) x ∂(ρ.map e) := by
      have hs' : MeasurableSet ((fun x => g * x) ⁻¹' s) := measurable_const_mul g hs
      rw [← lintegral_indicator_one hs']
      refine lintegral_congr fun x => ?_
      have := hval (g * x)
      simpa [Set.indicator] using this.symm
    obtain ⟨p, rfl⟩ := e.surjective g
    rw [h1, h2, hint (fun y => f ((e p : G1 F) * y)) (hf.comp (measurable_const_mul _)), hint f hf]
    simp only [he]
    exact M.borLeft F f hf p.2 p.1⟩
  exact {}
