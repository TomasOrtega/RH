import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

section

variable {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hμ`. Use `haveI := h1`. Use `haveI := h2`. Establish `hUm : MeasurableSet (U : Set G)` using `hU.measurableSet`. Establish `emb : MeasurableEmbedding (fun u : U => (u : G))` using `MeasurableEmbedding.subtype_coe hUm`.

Establish `hH : (μ.comap U.subtype).IsHaarMeasure` using `Measure.IsHaarMeasure.comap (mH := inferInstance) μ hU.isOpenEmbedding_subtypeVal`. Use `⟨hH, ⟨?_⟩⟩` and prove the remaining obligations. Use extensionality with `s hs`. Rewrite using `[Measure.inv_apply, emb.comap_apply, emb.comap_apply]`. Establish `e : (fun u : U => (u : G)) '' s⁻¹ = ((fun u : U => (u : G)) '' s)⁻¹`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨u⁻¹, hu, by simp⟩`. Introduce `hx`.

Take `⟨u, hu, hux⟩` from `hx`. Use `⟨u⁻¹, by simpa using hu, ?_⟩` and prove the remaining obligations. Establish `hux' : (u : G) = x⁻¹` using `hux`. Simplify using `[hux']`. Rewrite using `[e, Measure.measure_inv]`.
-/
private lemma uni_comap (μ : Measure G) (hμ : Uni μ) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    Uni (μ.comap fun u : U => (u : G)) := by
  obtain ⟨h1, h2⟩ := hμ
  haveI := h1
  haveI := h2
  have hUm : MeasurableSet (U : Set G) := hU.measurableSet
  have emb : MeasurableEmbedding (fun u : U => (u : G)) := MeasurableEmbedding.subtype_coe hUm
  have hH : (μ.comap U.subtype).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) μ hU.isOpenEmbedding_subtypeVal
  refine ⟨hH, ⟨?_⟩⟩
  ext s hs
  rw [Measure.inv_apply, emb.comap_apply, emb.comap_apply]
  have e : (fun u : U => (u : G)) '' s⁻¹ = ((fun u : U => (u : G)) '' s)⁻¹ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, hu, by simp⟩
    · intro hx
      obtain ⟨u, hu, hux⟩ := hx
      refine ⟨u⁻¹, by simpa using hu, ?_⟩
      have hux' : (u : G) = x⁻¹ := hux
      simp [hux']
  rw [e, Measure.measure_inv]

private def ext0 (U : Subgroup G) (r : U → ℝ≥0∞) : G → ℝ≥0∞ :=
  Function.extend (fun u : U => (u : G)) r 0

/- English proof (translation)
The claim follows from `Subtype.val_injective.extend_apply _ _ _`.
-/
private lemma ext0_coe (U : Subgroup G) (r : U → ℝ≥0∞) (u : U) : ext0 U r (u : G) = r u :=
  Subtype.val_injective.extend_apply _ _ _

/- English proof (translation)
Unfold `ext0`. Rewrite using `[Function.extend_apply']`. Both sides reduce to the same expression. Introduce and unpack `⟨u, rfl⟩`. Conclude with `hg u.2`.
-/
private lemma extendByZero_not_mem (U : Subgroup G) (r : U → ℝ≥0∞) {g : G} (hg : g ∉ U) : ext0 U r g = 0 := by
  unfold ext0
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨u, rfl⟩
    exact hg u.2

/- English proof (translation)
Establish `e : (fun t => ext0 U r (j t * u)) = ((U.comap j : Subgroup T) : Set T).indicator (fun t => ext0 U r (j t * u))`. Use function extensionality and compare the values at `t`. Distinguish the cases in `ht : t ∈ U.comap j`. Rewrite using `[Set.indicator_of_mem (by exact ht)]`. Rewrite using `[Set.indicator_of_notMem (by exact ht)]`.

Apply `extendByZero_not_mem` to reduce the goal to its premises. Introduce `hmem`. Apply `ht` to reduce the goal to its premises. Establish `h2 : j t = (j t * u) * (u : G)⁻¹` using `by group`. Rewrite using `[Subgroup.mem_comap, h2]`.

Conclude with `U.mul_mem hmem (U.inv_mem u.2)`. Establish `h` using `lintegral_subtype_comap hV (μ := ν) (fun t => ext0 U r (j t * u))`. Rewrite using `[e, lintegral_indicator hV, ← h, ← h₀ u]`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Establish `h3 : j (t : T) * (u : G) = ((i t * u : U) : G)` using `by simp [hi]`.

Rewrite using `[h3, ext0_coe]`.
-/
private lemma nrm_on_coset (j : T →* G) (ν : Measure T) (U : Subgroup G)
    (hV : MeasurableSet ((U.comap j : Subgroup T) : Set T)) (i : U.comap j →* U)
    (hi : ∀ t, (i t : G) = j t) (r : U → ℝ≥0∞)
    (h₀ : ∀ x, ∫⁻ t, r (i t * x) ∂(ν.comap fun t : U.comap j => (t : T)) = 1) (u : U) :
    ∫⁻ t, ext0 U r (j t * u) ∂ν = 1 := by
  have e : (fun t => ext0 U r (j t * u)) =
      ((U.comap j : Subgroup T) : Set T).indicator (fun t => ext0 U r (j t * u)) := by
    funext t
    by_cases ht : t ∈ U.comap j
    · rw [Set.indicator_of_mem (by exact ht)]
    · rw [Set.indicator_of_notMem (by exact ht)]
      apply extendByZero_not_mem
      intro hmem
      apply ht
      have h2 : j t = (j t * u) * (u : G)⁻¹ := by group
      rw [Subgroup.mem_comap, h2]
      exact U.mul_mem hmem (U.inv_mem u.2)
  have h := lintegral_subtype_comap hV (μ := ν) (fun t => ext0 U r (j t * u))
  rw [e, lintegral_indicator hV, ← h, ← h₀ u]
  refine lintegral_congr fun t => ?_
  have h3 : j (t : T) * (u : G) = ((i t * u : U) : G) := by simp [hi]
  rw [h3, ext0_coe]

open Classical in
/- English proof (translation)
Use `haveI := hν.2`. Use `haveI := hν.1`. Use `haveI : ν.IsMulRightInvariant := by`. Establish `h2 : (ν.inv).IsMulRightInvariant` using `inferInstance`. Rewrite `h2` using `[Measure.IsInvInvariant.inv_eq_self]`. Then use the resulting hypothesis.

Establish `hS : IsOpen (Set.range j * (U : Set G))` using `hU.mul_left`. Establish `hm : Measurable (ext0 U r)` using `(MeasurableEmbedding.subtype_coe hU.measurableSet).measurable_extend h₀.1 measurable_const`. Use `⟨hm.piecewise hS.measurableSet h'.1, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ Set.range j * (U : Set G)`. Take `⟨_, ⟨s, rfl⟩, u, hu, rfl⟩` from `hx`.

Establish `e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * (j s * u)) = ext0 U r (j (t * s) * u)`. Introduce `t`. Rewrite using `[Set.piecewise_eq_of_mem, map_mul, mul_assoc]`. Conclude with `⟨j (t * s), ⟨_, rfl⟩, u, hu, by simp [mul_assoc]⟩`. Use `Eq.trans (lintegral_congr e) ((lintegral_mul_right_eq_self (μ := ν) (fun t => ext0 U r (j t * u)) s).trans ?_)` and prove the remaining obligations.

Conclude with `nrm_on_coset j ν U hV i hi r h₀.2 ⟨u, hu⟩`. Establish `e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * x) = r' (j t * x)`. Introduce `t`. Apply `Set.piecewise_eq_of_notMem` to reduce the goal to its premises. Introduce `hm2`.

Apply `hx` to reduce the goal to its premises. Take `⟨_, ⟨s, rfl⟩, u, hu, hxe⟩` from `hm2`. Use `⟨j (t⁻¹ * s), ⟨_, rfl⟩, u, hu, ?_⟩` and prove the remaining obligations. Establish `hxe' : j s * u = j t * x` using `hxe`. Express the relevant statement in the definitionally equal form `j (t⁻¹ * s) * u = x`.

Rewrite using `[map_mul, map_inv, mul_assoc, hxe', inv_mul_cancel_left]`. Conclude with `(lintegral_congr e).trans (h'.2 x)`.
-/
private lemma isNrm_glue (j : T →* G) (ν : Measure T) (hν : Uni ν) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hV : MeasurableSet ((U.comap j : Subgroup T) : Set T))
    (i : U.comap j →* U) (hi : ∀ t, (i t : G) = j t) (r : U → ℝ≥0∞)
    (h₀ : IsNrm i (ν.comap fun t : U.comap j => (t : T)) r) (r' : G → ℝ≥0∞) (h' : IsNrm j ν r') :
    IsNrm j ν ((Set.range j * (U : Set G)).piecewise (ext0 U r) r') := by
  haveI := hν.2
  haveI := hν.1
  haveI : ν.IsMulRightInvariant := by
    have h2 : (ν.inv).IsMulRightInvariant := inferInstance
    rwa [Measure.IsInvInvariant.inv_eq_self] at h2
  have hS : IsOpen (Set.range j * (U : Set G)) := hU.mul_left
  have hm : Measurable (ext0 U r) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurable_extend h₀.1 measurable_const
  refine ⟨hm.piecewise hS.measurableSet h'.1, fun x => ?_⟩
  by_cases hx : x ∈ Set.range j * (U : Set G)
  · obtain ⟨_, ⟨s, rfl⟩, u, hu, rfl⟩ := hx
    have e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * (j s * u)) =
        ext0 U r (j (t * s) * u) := by
      intro t
      rw [Set.piecewise_eq_of_mem, map_mul, mul_assoc]
      exact ⟨j (t * s), ⟨_, rfl⟩, u, hu, by simp [mul_assoc]⟩
    refine Eq.trans (lintegral_congr e) ((lintegral_mul_right_eq_self (μ := ν)
      (fun t => ext0 U r (j t * u)) s).trans ?_)
    exact nrm_on_coset j ν U hV i hi r h₀.2 ⟨u, hu⟩
  · have e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * x) = r' (j t * x) := by
      intro t
      apply Set.piecewise_eq_of_notMem
      intro hm2
      apply hx
      obtain ⟨_, ⟨s, rfl⟩, u, hu, hxe⟩ := hm2
      refine ⟨j (t⁻¹ * s), ⟨_, rfl⟩, u, hu, ?_⟩
      have hxe' : j s * u = j t * x := hxe
      change j (t⁻¹ * s) * u = x
      rw [map_mul, map_inv, mul_assoc, hxe', inv_mul_cancel_left]
    exact (lintegral_congr e).trans (h'.2 x)

end

end UpperTheory.ConvolutionTheory.G

open MeasureTheory Topology UpperTheory.ConvolutionTheory.G in
/- English proof (translation)
Introduce `hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν h U hU i hi`. Take `⟨hμ, hj, hν⟩` from `id h`. Establish `hV : IsOpen ((U.comap j : Subgroup T) : Set T)` using `hU.preimage hj.continuous`. Establish `hUm : MeasurableSet (U : Set G)` using `hU.measurableSet`. Use `haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)`.

Use `haveI : SecondCountableTopology (U.comap j) := TopologicalSpace.Subtype.secondCountableTopology ((U.comap j : Subgroup T) : Set T)`. Use `haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : LocallyCompactSpace (U.comap j) := hV.isOpenEmbedding_subtypeVal.locallyCompactSpace`. Establish `hUc : IsClosedEmbedding (fun u : U => (u : G))` using `(Subgroup.isClosed_of_isOpen U hU).isClosedEmbedding_subtypeVal`. Establish `hVc : IsClosedEmbedding (fun t : U.comap j => (t : T))` using `(Subgroup.isClosed_of_isOpen _ hV).isClosedEmbedding_subtypeVal`.

Establish `hic : IsClosedEmbedding i`. Establish `h1 : IsClosedEmbedding ((fun u : U => (u : G)) ∘ i)`. Establish `h2 : ((fun u : U => (u : G)) ∘ i) = j ∘ (fun t : U.comap j => (t : T))`. Use function extensionality and compare the values at `t`. Conclude with `hi t`.

Rewrite using `[h2]`. Conclude with `hj.comp hVc`. Conclude with `(IsClosedEmbedding.of_comp_iff hUc).1 h1`. Establish `hs : Pair (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T))` using `⟨uni_comap μ hμ U hU, hic, uni_comap ν hν _ hV⟩`. Use `⟨hs, fun F hFm hFi hFs => ?_⟩` and prove the remaining obligations.

Take `⟨r₀, -, hr₀, -⟩` from `hN U (U.comap j) _ i _ hs`. Take `⟨r', -, hr', -⟩` from `hN G T μ j ν h`. Establish `hg` using `isNrm_glue j ν hν U hU hV.measurableSet i hi _ hr₀ _ hr'`. Take `⟨hQ1, -, hQ3⟩` from `hE G T μ j ν h F hFm hFi _ hg`. Establish `hFm' : Measurable (fun u : U => F u)` using `hFm.comp measurable_subtype_coe`.

Establish `hFi' : ∀ (t : U.comap j) (g : U), F ((i t * g : U) : G) = F g`. Introduce `t g`. Simplify using `[hi, hFi]`. Take `⟨hq1, -, hq3⟩` from `hE U (U.comap j) _ i _ hs (fun u => F u) hFm' hFi' _ hr₀`. Establish `key : (fun x => F x * ((((Set.range j * (U : Set G)).piecewise (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) = (U : Set G).indicator (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ))`.

Use function extensionality and compare the values at `x`. Distinguish the cases in `hxU : x ∈ (U : Set G)`. Rewrite using `[Set.indicator_of_mem hxU, Set.piecewise_eq_of_mem]`. Conclude with `⟨1, ⟨1, map_one j⟩, x, hxU, one_mul x⟩`. Rewrite using `[Set.indicator_of_notMem hxU]`.

Distinguish the cases in `hxS : x ∈ Set.range j * (U : Set G)`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ hxS, extendByZero_not_mem U _ hxU]`. Simplify using the standard rewrite rules. Establish `: F x = 0`. Assume the negation of the conclusion as `h0`.

Conclude with `hxS (hFs x h0)`. Simplify using `[this]`. Establish `cmp : (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ)) ∘ (fun u : U => (u : G)) = fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ)`. Use function extensionality and compare the values at `u`. Simplify using `only [Function.comp]`.

Rewrite using `[show ext0 U (fun u => (r₀ u : ENNReal)) (u : G) = _ from ext0_coe U _ u]`. Establish `i1 : Integrable (fun x => F x * ((((Set.range j * (U : Set G)).piecewise (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) μ ↔ Integrable (fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ)) (μ.comap fun u : U => (u : G))`. Rewrite using `[key, integrable_indicator_iff hUm, integrableOn_iff_comap_subtypeVal hUm]`. Conclude with `Iff.of_eq (congrArg (fun f => Integrable f (μ.comap fun u : U => (u : G))) cmp)`. Establish `i2 : ∫ x, F x * ((((Set.range j * (U : Set G)).piecewise (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ) ∂μ = ∫ u : U, F u * (((r₀ u : ENNReal)).toReal : ℂ) ∂(μ.comap fun u : U => (u : G))`.

Rewrite using `[key, integral_indicator hUm, ← integral_subtype_comap hUm]`. Conclude with `congrArg (fun f => ∫ u : U, f u ∂(μ.comap fun u : U => (u : G))) cmp`. Conclude with `⟨hQ1.trans (i1.trans hq1.symm), hQ3.trans (i2.trans hq3.symm)⟩`.
-/
theorem UpperTheory.ConvolutionTheory.G.quotOpen_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotOpen := by
  classical
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν h U hU i hi
  obtain ⟨hμ, hj, hν⟩ := id h
  have hV : IsOpen ((U.comap j : Subgroup T) : Set T) := hU.preimage hj.continuous
  have hUm : MeasurableSet (U : Set G) := hU.measurableSet
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : SecondCountableTopology (U.comap j) :=
    TopologicalSpace.Subtype.secondCountableTopology ((U.comap j : Subgroup T) : Set T)
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (U.comap j) := hV.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hUc : IsClosedEmbedding (fun u : U => (u : G)) :=
    (Subgroup.isClosed_of_isOpen U hU).isClosedEmbedding_subtypeVal
  have hVc : IsClosedEmbedding (fun t : U.comap j => (t : T)) :=
    (Subgroup.isClosed_of_isOpen _ hV).isClosedEmbedding_subtypeVal
  have hic : IsClosedEmbedding i := by
    have h1 : IsClosedEmbedding ((fun u : U => (u : G)) ∘ i) := by
      have h2 : ((fun u : U => (u : G)) ∘ i) = j ∘ (fun t : U.comap j => (t : T)) := by
        funext t
        exact hi t
      rw [h2]
      exact hj.comp hVc
    exact (IsClosedEmbedding.of_comp_iff hUc).1 h1
  have hs : Pair (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) :=
    ⟨uni_comap μ hμ U hU, hic, uni_comap ν hν _ hV⟩
  refine ⟨hs, fun F hFm hFi hFs => ?_⟩
  obtain ⟨r₀, -, hr₀, -⟩ := hN U (U.comap j) _ i _ hs
  obtain ⟨r', -, hr', -⟩ := hN G T μ j ν h
  have hg := isNrm_glue j ν hν U hU hV.measurableSet i hi _ hr₀ _ hr'
  obtain ⟨hQ1, -, hQ3⟩ := hE G T μ j ν h F hFm hFi _ hg
  have hFm' : Measurable (fun u : U => F u) := hFm.comp measurable_subtype_coe
  have hFi' : ∀ (t : U.comap j) (g : U), F ((i t * g : U) : G) = F g := by
    intro t g
    simp [hi, hFi]
  obtain ⟨hq1, -, hq3⟩ := hE U (U.comap j) _ i _ hs (fun u => F u) hFm' hFi' _ hr₀
  have key : (fun x => F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) =
      (U : Set G).indicator (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ)) := by
    funext x
    by_cases hxU : x ∈ (U : Set G)
    · rw [Set.indicator_of_mem hxU, Set.piecewise_eq_of_mem]
      exact ⟨1, ⟨1, map_one j⟩, x, hxU, one_mul x⟩
    · rw [Set.indicator_of_notMem hxU]
      by_cases hxS : x ∈ Set.range j * (U : Set G)
      · rw [Set.piecewise_eq_of_mem _ _ _ hxS, extendByZero_not_mem U _ hxU]
        simp
      · have : F x = 0 := by
          by_contra h0
          exact hxS (hFs x h0)
        simp [this]
  have cmp : (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ)) ∘
      (fun u : U => (u : G)) = fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ) := by
    funext u
    simp only [Function.comp]
    rw [show ext0 U (fun u => (r₀ u : ENNReal)) (u : G) = _ from ext0_coe U _ u]
  have i1 : Integrable (fun x => F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) μ ↔
      Integrable (fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ))
        (μ.comap fun u : U => (u : G)) := by
    rw [key, integrable_indicator_iff hUm, integrableOn_iff_comap_subtypeVal hUm]
    exact Iff.of_eq (congrArg (fun f => Integrable f (μ.comap fun u : U => (u : G))) cmp)
  have i2 : ∫ x, F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ) ∂μ =
      ∫ u : U, F u * (((r₀ u : ENNReal)).toReal : ℂ) ∂(μ.comap fun u : U => (u : G)) := by
    rw [key, integral_indicator hUm, ← integral_subtype_comap hUm]
    exact congrArg (fun f => ∫ u : U, f u ∂(μ.comap fun u : U => (u : G))) cmp
  exact ⟨hQ1.trans (i1.trans hq1.symm), hQ3.trans (i2.trans hq3.symm)⟩
