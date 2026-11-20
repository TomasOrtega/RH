import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedChartHolomorphicCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace GlobalTheory.Mean4O.CoverInt

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e}

/- English proof (translation)
The claim follows from `have : SecondCountableTopology (Pts Y (I.ε a)) := CxPts.secondCountableTopology_of_isProjOver _ Y.isProjOver (I.pt a).isEmbedding.secondCountableTopology`.
-/
theorem secondCountable (I : ManIs M Y) (a : Fin (M.n + 1)) : SecondCountableTopology (M.X a) :=
  have : SecondCountableTopology (Pts Y (I.ε a)) :=
    CxPts.secondCountableTopology_of_isProjOver _ Y.isProjOver
  (I.pt a).isEmbedding.secondCountableTopology

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `A.cover x`. Establish `h` using `(hf j).continuousOn`. Rewrite `h` using `[preimage_univ, inter_univ]`. Establish `hc` using `(h.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp ((A.chart j).continuousAt hj)`.

Use `hc.congr (eventually_of_mem ((A.chart j).open_source.mem_nhds hj) fun y hy => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, (A.chart j).left_inv hy]`.
-/
theorem continuous_of_smooth' {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {f : X → ℝ}
    (hf : A.Smooth f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hj⟩ := A.cover x
  have h := (hf j).continuousOn
  rw [preimage_univ, inter_univ] at h
  have hc := (h.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp
    ((A.chart j).continuousAt hj)
  refine hc.congr (eventually_of_mem ((A.chart j).open_source.mem_nhds hj) fun y hy => ?_)
  simp only [Function.comp_apply, (A.chart j).left_inv hy]

variable (I : ManIs M Y) {a : Fin (M.n + 1)} {P : LocPot (M.X a)} {j : Fin (M.A a).n}
  {c : AlgChart Y.str (I.ε a) e}

/- English proof (translation)
Rewrite using `[hc]`. Both sides reduce to the same expression.
-/
theorem chart_symm_eq (hc : (M.A a).chart j = (I.pt a).transOpenPartialHomeomorph c.finChart)
    (z : Fin e → ℂ) : ((M.A a).chart j).symm z = (tChart I c).symm (FinChart.toV e z) := by
  rw [hc]; rfl

/- English proof (translation)
Rewrite using `[hc]`. Both sides reduce to the same expression.
-/
theorem chart_target_eq (hc : (M.A a).chart j = (I.pt a).transOpenPartialHomeomorph c.finChart) :
    ((M.A a).chart j).target = FinChart.toV e ⁻¹' (tChart I c).target := by
  rw [hc]; rfl

/- English proof (translation)
Rewrite using `[hc]`. Both sides reduce to the same expression.
-/
theorem chart_source_eq (hc : (M.A a).chart j = (I.pt a).transOpenPartialHomeomorph c.finChart) :
    ((M.A a).chart j).source = (tChart I c).source := by
  rw [hc]; rfl

/- English proof (translation)
Use `set x := ((M.A a).chart j).symm z with hx`. Establish `hz' : FinChart.toV e z ∈ (tChart I c).target` using `by rwa [chart_target_eq I hc] at hz`. Establish `hr : c.e (I.pt a x) = FinChart.toV e z`. Rewrite using `[hx, chart_symm_eq I hc]`. Conclude with `(tChart I c).right_inv hz'`.

Establish `hs` using `potSmoothAt (M.A a) P hP x j (y := z) ⟨hz, P.mem_U x⟩`. Use `set h : ReciprocityTheory.L2DbarEstimates.V e → ℝ := fun v => 2 * P.φ x ((I.pt a).symm (c.e.symm v)) with hh`. Establish `hcomp : h ∘ FinChart.toV e = fun w => 2 * (P.φ x ∘ ((M.A a).chart j).symm) w`. Use function extensionality and compare the values at `w`. Simplify using `only [hh, Function.comp_apply, chart_symm_eq I hc]`.

Both sides reduce to the same expression. Establish `hsd : ContDiffAt ℝ 2 h (FinChart.toV e z)`. Establish `h1 : ContDiffAt ℝ 2 (fun w => 2 * (P.φ x ∘ ((M.A a).chart j).symm) w) z` using `contDiffAt_const.mul hs`. Establish `h2` using `h1.comp (FinChart.toV e z) (f := (FinChart.toV e).symm) (by simpa using (FinChart.toV e).symm.contDiff.contDiffAt)`. Use `h2.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)` and prove the remaining obligations.

Use `congrFun hcomp ((FinChart.toV e).symm v)` as an intermediate fact. Simplify using `only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at this ⊢`. Conclude with `this`. Establish `hdet` using `ChernMA.cHess_eq_hessC hsd`. Unfold `potDens`.

Move the coercions through the operations in `at hdet ⊢`. Rewrite using `[hr]`. Simplify using `only [hh] at hdet`. Move the coercions through the operations in `at hdet`. Rewrite using `[hdet, hcomp, hessC_const_mul', Matrix.det_smul, Fintype.card_fin]`.

Rewrite using `[locDens, maDens, ReciprocityTheory.AnForm.A.mdisc_const, ← Complex.ofReal_pow, Complex.re_ofReal_mul, div_pow]`. Establish `e1 : (fun y' => P.φ (((M.A a).chart j).symm z) (((M.A a).chart j).symm y')) = P.φ x ∘ ((M.A a).chart j).symm` using `rfl`. Rewrite using `[e1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem locDens_eq_potDens (hP : IsPotential (M.A a) P)
    (hc : (M.A a).chart j = (I.pt a).transOpenPartialHomeomorph c.finChart) {z : Fin e → ℂ}
    (hz : z ∈ ((M.A a).chart j).target) :
    locDens (M.A a) (fun _ => P) j z = potDens I P c (((M.A a).chart j).symm z) := by
  set x := ((M.A a).chart j).symm z with hx
  have hz' : FinChart.toV e z ∈ (tChart I c).target := by rwa [chart_target_eq I hc] at hz
  have hr : c.e (I.pt a x) = FinChart.toV e z := by
    rw [hx, chart_symm_eq I hc]
    exact (tChart I c).right_inv hz'
  have hs := potSmoothAt (M.A a) P hP x j (y := z) ⟨hz, P.mem_U x⟩
  set h : ReciprocityTheory.L2DbarEstimates.V e → ℝ := fun v => 2 * P.φ x ((I.pt a).symm (c.e.symm v)) with hh
  have hcomp : h ∘ FinChart.toV e = fun w => 2 * (P.φ x ∘ ((M.A a).chart j).symm) w := by
    funext w
    simp only [hh, Function.comp_apply, chart_symm_eq I hc]
    rfl
  have hsd : ContDiffAt ℝ 2 h (FinChart.toV e z) := by
    have h1 : ContDiffAt ℝ 2 (fun w => 2 * (P.φ x ∘ ((M.A a).chart j).symm) w) z :=
      contDiffAt_const.mul hs
    have h2 := h1.comp (FinChart.toV e z) (f := (FinChart.toV e).symm)
      (by simpa using (FinChart.toV e).symm.contDiff.contDiffAt)
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
    have := congrFun hcomp ((FinChart.toV e).symm v)
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at this ⊢
    exact this
  have hdet := ChernMA.cHess_eq_hessC hsd
  unfold potDens
  push_cast at hdet ⊢
  rw [hr]
  simp only [hh] at hdet
  push_cast at hdet
  rw [hdet, hcomp, hessC_const_mul', Matrix.det_smul, Fintype.card_fin]
  rw [locDens, maDens, ReciprocityTheory.AnForm.A.mdisc_const, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    div_pow]
  have e1 : (fun y' => P.φ (((M.A a).chart j).symm z) (((M.A a).chart j).symm y')) =
    P.φ x ∘ ((M.A a).chart j).symm := rfl
  rw [e1]
  field_simp

variable [SecondCountableTopology (M.X a)]

/- English proof (translation)
Take `⟨hd, hρ⟩` from `GlobalTheory.T.transported_chart_holomorphic_compat F Y e M I a P hP`. Use `glueMeas_apply _ _ hd (fun c c' y hy hy' => ?_) c hT h` and prove the remaining obligations. Rewrite using `[hρ c c' y hy hy', ← ENNReal.ofReal_mul (sq_nonneg _)]`. Put the polynomial expressions in normal form.
-/
theorem potMeas_apply (hP : IsPotential (M.A a) P) (s : ℤˣ) (c : AlgChart Y.str (I.ε a) e)
    {T : Set (M.X a)} (hT : MeasurableSet T) (h : T ⊆ (tChart I c).source) :
    potMeas I P s T = chartMeas (tChart I c) (fun x => ENNReal.ofReal ((s : ℤ) * potDens I P c x)) T := by
  obtain ⟨hd, hρ⟩ := GlobalTheory.T.transported_chart_holomorphic_compat F Y e M I a P hP
  refine glueMeas_apply _ _ hd (fun c c' y hy hy' => ?_) c hT h
  rw [hρ c c' y hy hy', ← ENNReal.ofReal_mul (sq_nonneg _)]
  ring_nf

/- English proof (translation)
Use extensionality with `T hT`. Establish `ht` using `((M.A a).chart j).open_target.measurableSet`. Establish `hs : AEMeasurable ((M.A a).chart j).symm (volume.restrict ((M.A a).chart j).target)` using `((M.A a).chart j).continuousOn_symm.aemeasurable ht`. Establish `hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin e → ℂ))` using `MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin e → ℂ)).symm (volume_preserving_ofLp_complex (Fin e))`. Establish `hsub : (tChart I c).source ∩ T ⊆ (tChart I c).source` using `inter_subset_left`.

Establish `hm` using `measurableSet_image (tChart I c) ((tChart I c).open_source.measurableSet.inter hT) hsub`. Rewrite using `[Measure.restrict_apply hT, inter_comm, chart_source_eq I hc, potMeas_apply I hP s c ((tChart I c).open_source.measurableSet.inter hT) hsub, chartMeas_apply_of_subset _ _ ((tChart I c).open_source.measurableSet.inter hT) hsub, Measure.map_apply_of_aemeasurable (hs.mono_ac (withDe …`. Establish `hpre : ((M.A a).chart j).symm ⁻¹' T ∩ ((M.A a).chart j).target = MeasurableEquiv.toLp 2 (Fin e → ℂ) ⁻¹' ((tChart I c) '' ((tChart I c).source ∩ T))`. Rewrite using `[(tChart I c).image_source_inter_eq', inter_comm, chart_target_eq I hc]`. Use extensionality with `z`.

Simplify using `only [mem_inter_iff, mem_preimage, chart_symm_eq I hc]`. Both sides reduce to the same expression. Rewrite using `[hpre, ← hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)]`. Use `setLIntegral_congr_fun (hp.measurable hm) fun z hz => ?_` and prove the remaining obligations. Establish `hz' : z ∈ ((M.A a).chart j).target`.

Rewrite using `[chart_target_eq I hc]`. Take `⟨y, hy, hyz⟩` from `hz`. Use `(tChart I c).map_source hy.1` as an intermediate fact. Rewrite `this` using `[hyz]`. Conclude with `this`.

Rewrite using `[locDens_eq_potDens I hP hc hz', chart_symm_eq I hc]`. Both sides reduce to the same expression.
-/
theorem restrict_potMeas (hP : IsPotential (M.A a) P) (s : ℤˣ)
    (hc : (M.A a).chart j = (I.pt a).transOpenPartialHomeomorph c.finChart) :
    (potMeas I P s).restrict ((M.A a).chart j).source =
      ((volume.restrict ((M.A a).chart j).target).withDensity fun z =>
        ENNReal.ofReal ((s : ℤ) * locDens (M.A a) (fun _ => P) j z)).map ((M.A a).chart j).symm := by
  ext T hT
  have ht := ((M.A a).chart j).open_target.measurableSet
  have hs : AEMeasurable ((M.A a).chart j).symm (volume.restrict ((M.A a).chart j).target) :=
    ((M.A a).chart j).continuousOn_symm.aemeasurable ht
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin e → ℂ)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin e → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin e))
  have hsub : (tChart I c).source ∩ T ⊆ (tChart I c).source := inter_subset_left
  have hm := measurableSet_image (tChart I c) ((tChart I c).open_source.measurableSet.inter hT) hsub
  rw [Measure.restrict_apply hT, inter_comm, chart_source_eq I hc,
    potMeas_apply I hP s c ((tChart I c).open_source.measurableSet.inter hT) hsub,
    chartMeas_apply_of_subset _ _ ((tChart I c).open_source.measurableSet.inter hT) hsub,
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply', Measure.restrict_restrict' ht]
  have hpre : ((M.A a).chart j).symm ⁻¹' T ∩ ((M.A a).chart j).target =
      MeasurableEquiv.toLp 2 (Fin e → ℂ) ⁻¹' ((tChart I c) '' ((tChart I c).source ∩ T)) := by
    rw [(tChart I c).image_source_inter_eq', inter_comm, chart_target_eq I hc]
    ext z
    simp only [mem_inter_iff, mem_preimage, chart_symm_eq I hc]
    rfl
  rw [hpre, ← hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
  refine setLIntegral_congr_fun (hp.measurable hm) fun z hz => ?_
  have hz' : z ∈ ((M.A a).chart j).target := by
    rw [chart_target_eq I hc]
    obtain ⟨y, hy, hyz⟩ := hz
    have := (tChart I c).map_source hy.1
    rw [hyz] at this
    exact this
  rw [locDens_eq_potDens I hP hc hz', chart_symm_eq I hc]
  rfl

/- English proof (translation)
Establish `hm (j) : Measurable fun y => ENNReal.ofReal (Q.χ j y)` using `ENNReal.measurable_ofReal.comp (continuous_of_smooth' _ (Q.smooth j)).measurable`. Establish `key (j) : chartPartMeasure (M.A a) Q (fun _ => P) (s : ℤ) j = (potMeas I P s).withDensity fun y => ENNReal.ofReal (Q.χ j y)`. Take `⟨c, hc⟩` from `I.alg a j`. Establish `ht` using `((M.A a).chart j).open_target.measurableSet`. Establish `hs : AEMeasurable ((M.A a).chart j).symm (volume.restrict ((M.A a).chart j).target)` using `((M.A a).chart j).continuousOn_symm.aemeasurable ht`.

Establish `e : (fun y => ENNReal.ofReal (Q.χ j y)) = ((M.A a).chart j).source.indicator fun y => ENNReal.ofReal (Q.χ j y)`. Use `(indicator_eq_self.2 fun y hy => Q.tsupport_subset j (subset_tsupport _ ?_)).symm` and prove the remaining obligations. Conclude with `fun h0 => hy (by simp [h0])`. Establish `hd : AEMeasurable (fun z => ENNReal.ofReal (((s : ℤ) : ℝ) * locDens (M.A a) (fun _ => P) j z)) (volume.restrict ((M.A a).chart j).target)` using `(((locDensCont (M.A a) _ (fun _ => hP) j).aemeasurable ht).const_mul _).ennreal_ofReal`. Rewrite using `[e, withDensity_indicator ((M.A a).chart j).open_source.measurableSet, restrict_potMeas I hP s hc, ChernMA.map_withDensity (hs.mono_ac (withDensity_absolutelyContinuous _ _)) (hm j), ← withDensity_mul₀ hd ((hm j).comp_aemeasurable hs), chartPartMeasure]`.

Use `congrArg _ (withDensity_congr_ae (ae_restrict_of_forall_mem ht fun z hz => ?_))` and prove the remaining obligations. Simplify using `only [Pi.mul_apply, Function.comp_apply]`. Rewrite using `[mul_left_comm, ENNReal.ofReal_mul (Q.nonneg _ _), mul_comm]`. Use extensionality with `T hT`. Simplify using `only [key, Measure.coe_finsetSum, Finset.sum_apply, withDensity_apply _ hT]`.

Rewrite using `[← lintegral_finsetSum _ fun j _ => hm j, ← setLIntegral_one]`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_sum_of_nonneg fun j _ => Q.nonneg j y, Q.sum_eq_one, ENNReal.ofReal_one]`.
-/
theorem potMeas_eq_sum (hP : IsPotential (M.A a) P) (Q : ChartPartition (M.A a)) (s : ℤˣ) :
    potMeas I P s = ∑ j, chartPartMeasure (M.A a) Q (fun _ => P) (s : ℤ) j := by
  have hm (j) : Measurable fun y => ENNReal.ofReal (Q.χ j y) :=
    ENNReal.measurable_ofReal.comp (continuous_of_smooth' _ (Q.smooth j)).measurable
  have key (j) : chartPartMeasure (M.A a) Q (fun _ => P) (s : ℤ) j =
      (potMeas I P s).withDensity fun y => ENNReal.ofReal (Q.χ j y) := by
    obtain ⟨c, hc⟩ := I.alg a j
    have ht := ((M.A a).chart j).open_target.measurableSet
    have hs : AEMeasurable ((M.A a).chart j).symm (volume.restrict ((M.A a).chart j).target) :=
      ((M.A a).chart j).continuousOn_symm.aemeasurable ht
    have e : (fun y => ENNReal.ofReal (Q.χ j y)) =
        ((M.A a).chart j).source.indicator fun y => ENNReal.ofReal (Q.χ j y) := by
      refine (indicator_eq_self.2 fun y hy => Q.tsupport_subset j (subset_tsupport _ ?_)).symm
      exact fun h0 => hy (by simp [h0])
    have hd : AEMeasurable (fun z => ENNReal.ofReal (((s : ℤ) : ℝ) * locDens (M.A a) (fun _ => P) j z))
        (volume.restrict ((M.A a).chart j).target) :=
      (((locDensCont (M.A a) _ (fun _ => hP) j).aemeasurable ht).const_mul _).ennreal_ofReal
    rw [e, withDensity_indicator ((M.A a).chart j).open_source.measurableSet, restrict_potMeas I hP s hc,
      ChernMA.map_withDensity (hs.mono_ac (withDensity_absolutelyContinuous _ _)) (hm j),
      ← withDensity_mul₀ hd ((hm j).comp_aemeasurable hs), chartPartMeasure]
    refine congrArg _ (withDensity_congr_ae (ae_restrict_of_forall_mem ht fun z hz => ?_))
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [mul_left_comm, ENNReal.ofReal_mul (Q.nonneg _ _), mul_comm]
  ext T hT
  simp only [key, Measure.coe_finsetSum, Finset.sum_apply, withDensity_apply _ hT]
  rw [← lintegral_finsetSum _ fun j _ => hm j, ← setLIntegral_one]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => Q.nonneg j y, Q.sum_eq_one, ENNReal.ofReal_one]

/- English proof (translation)
Introduce `F _ _ Y e M I a P hP f hf`. Use `secondCountable I a` as an intermediate fact. Establish `hΦ : ∀ _ : Fin e, IsPotential (M.A a) P` using `fun _ => hP`. Establish `hi` using `mIntegrableCont (M.A a) _ hΦ f hf`. Use `set Q := (existsPartition (M.A a)).some`.

Establish `h1` using `fun s j => integral_chartPartMeasure (M.A a) Q _ hΦ s j f hf.measurable hi`. Establish `h2 (s : ℝ) (j) : IntegrableOn (fun y => f (((M.A a).chart j).symm y) * max (s * (Q.χ j (((M.A a).chart j).symm y) * locDens (M.A a) (fun _ => P) j y)) 0) ((M.A a).chart j).target`. Take `⟨hK, hKT, h0⟩` from `chart_weight_compact (M.A a) Q (fun _ => P) j`. Establish `hχ : ContinuousOn (fun y => Q.χ j (((M.A a).chart j).symm y)) ((M.A a).chart j).target` using `(Q.smooth j j).continuousOn.mono fun y hy => ⟨hy, mem_univ _⟩`. Use `((((hf.comp_continuousOn ((M.A a).chart j).continuousOn_symm).mul ((continuousOn_const.mul (hχ.mul (locDensCont (M.A a) _ hΦ j))).sup continuousOn_const)).mono hKT).integrableOn_compact hK).of_forall_sdiff_eq_zero ((M.A a).chart j).open_target.measurableSet fun y hy => ?_` and prove the remaining obligations.

Simplify using `[h0 y hy.1 hy.2]`. Rewrite using `[potMeas_eq_sum I hP Q, potMeas_eq_sum I hP Q, integral_finsetSum_measure fun j _ => (h1 _ j).1, integral_finsetSum_measure fun j _ => (h1 _ j).1, ← Finset.sum_sub_distrib, mInt, dif_pos (existsPartition (M.A a)), integralWith]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[(h1 _ j).2, (h1 _ j).2, ← integral_sub (h2 _ j) (h2 _ j)]`. Use `integral_congr_ae (ae_of_all _ fun y => ?_)` and prove the remaining obligations.

Simplify using `only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg]`. Rewrite using `[one_mul, neg_one_mul, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mInt_eq_potMeas : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e)
    (I : ManIs M Y) (a : Fin (M.n + 1)) (P : LocPot (M.X a)), IsPotential (M.A a) P →
    ∀ g : M.X a → ℝ, Continuous g →
      mInt (M.A a) (fun _ => P) g = ∫ x, g x ∂(potMeas I P 1) - ∫ x, g x ∂(potMeas I P (-1)) := by
  intro F _ _ Y e M I a P hP f hf
  have := secondCountable I a
  have hΦ : ∀ _ : Fin e, IsPotential (M.A a) P := fun _ => hP
  have hi := mIntegrableCont (M.A a) _ hΦ f hf
  set Q := (existsPartition (M.A a)).some
  have h1 := fun s j => integral_chartPartMeasure (M.A a) Q _ hΦ s j f hf.measurable hi
  have h2 (s : ℝ) (j) : IntegrableOn (fun y => f (((M.A a).chart j).symm y) * max (s * (Q.χ j
      (((M.A a).chart j).symm y) * locDens (M.A a) (fun _ => P) j y)) 0) ((M.A a).chart j).target := by
    obtain ⟨hK, hKT, h0⟩ := chart_weight_compact (M.A a) Q (fun _ => P) j
    have hχ : ContinuousOn (fun y => Q.χ j (((M.A a).chart j).symm y)) ((M.A a).chart j).target :=
      (Q.smooth j j).continuousOn.mono fun y hy => ⟨hy, mem_univ _⟩
    refine ((((hf.comp_continuousOn ((M.A a).chart j).continuousOn_symm).mul ((continuousOn_const.mul
      (hχ.mul (locDensCont (M.A a) _ hΦ j))).sup continuousOn_const)).mono hKT).integrableOn_compact
      hK).of_forall_sdiff_eq_zero ((M.A a).chart j).open_target.measurableSet fun y hy => ?_
    simp [h0 y hy.1 hy.2]
  rw [potMeas_eq_sum I hP Q, potMeas_eq_sum I hP Q, integral_finsetSum_measure fun j _ => (h1 _ j).1,
    integral_finsetSum_measure fun j _ => (h1 _ j).1, ← Finset.sum_sub_distrib, mInt,
    dif_pos (existsPartition (M.A a)), integralWith]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(h1 _ j).2, (h1 _ j).2, ← integral_sub (h2 _ j) (h2 _ j)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg]
  rw [one_mul, neg_one_mul, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  ring

end GlobalTheory.Mean4O.CoverInt
