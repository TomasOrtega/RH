import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

/- English proof (translation)
Introduce `n m h J hJ hm hmn hfin π A hA g hg`. Establish `hCover : ConeGraphCover.Statement` using `ConeGraphCover.proof ConeFiniteFibreDim.proof (ConeTangentDim.proof (ConeKrullDimLe.proof ConeFiniteFibreDim.proof) NullSmaller.full (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)) (ConeSmoothLocalGraph.proof PolyLocalGenerators.proof Holom …`. Establish `hArea : GraphAreaFibre.Statement` using `GraphAreaFibre.proof (GraphAreaIntegral.proof GraphAreaHolomorphic.full) TangentJacComp.proof AreaMultiplicityWeight.proof`. Take `⟨e, Ω, Φ, hpc, hnull⟩` from `hCover n m h J hJ hm hmn hfin`. Set `S : ℕ → Set (EuclideanSpace ℂ (Fin n))` to `fun i => graphPt (e i) (Φ i) '' Ω i`.

Set `D₀` to `disjointed S`. Set `D : ℕ → Set (EuclideanSpace ℂ (Fin n))` to `fun i => D₀ i ∩ A`. Establish `hSm : ∀ i, MeasurableSet (S i)` using `fun i => (hpc i).1.measurableSet.image_of_continuousOn_injOn (continuousOn_graphPt _ (hpc i).2.1.continuousOn) (graphPt_injective_of_graphBase _ _).injOn`. Establish `hD₀m : ∀ i, MeasurableSet (D₀ i)` using `MeasurableSet.disjointed hSm`. Establish `hDm : ∀ i, MeasurableSet (D i)` using `fun i => (hD₀m i).inter hA`.

Establish `hD₀S : ∀ i, D₀ i ⊆ S i` using `disjointed_subset S`. Establish `hDS : ∀ i, D i ⊆ S i` using `fun i => Set.inter_subset_left.trans (hD₀S i)`. Establish `hDd : Pairwise (Function.onFun Disjoint D)` using `fun i j hij => (disjoint_disjointed S hij).mono Set.inter_subset_left Set.inter_subset_left`. Establish `hU₀ : ⋃ i, D₀ i = ⋃ i, S i` using `iUnion_disjointed`. Establish `hUC₀ : ⋃ i, S i ⊆ coneSet h J` using `Set.iUnion_subset fun i => (hpc i).2.2.1`.

Establish `hUC : ⋃ i, D i ⊆ coneSet h J ∩ A` using `Set.iUnion_subset fun i y hy => ⟨hUC₀ (hU₀ ▸ Set.mem_iUnion.2 ⟨i, hy.1⟩), hy.2⟩`. Establish `hN : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) ((coneSet h J ∩ A) \ ⋃ i, D i) = 0`. Use `measure_mono_null ?_ hnull` and prove the remaining obligations. Introduce and unpack `y ⟨⟨hyC, hyA⟩, hyD⟩`. Use `⟨hyC, fun hyS => hyD ?_⟩` and prove the remaining obligations.

Rewrite `hyS` using `[← hU₀]`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hyS`. Conclude with `Set.mem_iUnion.2 ⟨i, hi, hyA⟩`. Establish `hCae : (coneSet h J ∩ A : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)] ⋃ i, D i` using `ae_eq_set.2 ⟨hN, by rw [Set.sdiff_eq_empty.2 hUC]; exact measure_empty⟩`. Establish `hpiece` using `fun i => hArea m (n - m) n (e i) (Ω i) (Φ i) (hpc i).1 (hpc i).2.1 (D i) (hDS i) (hDm i) (coneTangent h J) (fun x hx _ => (hpc i).2.2.2 x hx) π`.

Establish `hcount : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))), cntOver (coneSet h J ∩ A) π w * g w = ∑' i, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w` using `by filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_linProj_image_null π hN)] with w hw`. Rewrite using `[ENNReal.tsum_mul_right, cntOver, ptsOver, ← encard_iUnion_disjoint_nat]`. Use `congr 3`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_iUnion]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, rfl⟩`. Assume the negation of the conclusion as `hne`. Conclude with `hw ⟨y, ⟨hy, fun hyD => hne (by`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hyD`.

Conclude with `⟨i, hi, rfl⟩)⟩, rfl⟩`. Introduce and unpack `⟨i, hi, hw'⟩`. Conclude with `⟨hUC (Set.mem_iUnion.2 ⟨i, hi⟩), hw'⟩`. Introduce `i j hij`. Conclude with `(hDd hij).mono (fun y hy => hy.1) (fun y hy => hy.1)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Measure.restrict_congr_set hCae, lintegral_iUnion hDm hDd, ENNReal.tsum_mul_left]`. Use `_ = ∑' i, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) * ∫⁻ w, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w := tsum_congr fun i => (hpiece i).2 g hg`. Use `_ = Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) * ∫⁻ w, cntOver (coneSet h J ∩ A) π w * g w := by`. Rewrite using `[ENNReal.tsum_mul_left, ← lintegral_tsum (f := fun i w => (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w) fun i => (hpiece i).1.mul hg.aemeasurable, lintegral_congr_ae hcount]`.
-/
theorem coneArea_inter : ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
  (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ (π : Fin m → Fin n → ℂ) (A : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet A →
  ∀ g : EuclideanSpace ℂ (Fin m) → ℝ≥0∞, Measurable g →
    volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J ∩ A, g (linProj π y) * ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ w : EuclideanSpace ℂ (Fin m), cntOver (coneSet h J ∩ A) π w * g w := by
  intro n m h J hJ hm hmn hfin π A hA g hg
  have hCover : ConeGraphCover.Statement := ConeGraphCover.proof ConeFiniteFibreDim.proof
    (ConeTangentDim.proof (ConeKrullDimLe.proof ConeFiniteFibreDim.proof) NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
    (ConeSmoothLocalGraph.proof PolyLocalGenerators.proof HolomorphicImplicitGraph.proof)
  have hArea : GraphAreaFibre.Statement :=
    GraphAreaFibre.proof (GraphAreaIntegral.proof GraphAreaHolomorphic.full) TangentJacComp.proof
      AreaMultiplicityWeight.proof
  obtain ⟨e, Ω, Φ, hpc, hnull⟩ := hCover n m h J hJ hm hmn hfin
  let S : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => graphPt (e i) (Φ i) '' Ω i
  let D₀ := disjointed S
  let D : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => D₀ i ∩ A
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    (hpc i).1.measurableSet.image_of_continuousOn_injOn
      (continuousOn_graphPt _ (hpc i).2.1.continuousOn) (graphPt_injective_of_graphBase _ _).injOn
  have hD₀m : ∀ i, MeasurableSet (D₀ i) := MeasurableSet.disjointed hSm
  have hDm : ∀ i, MeasurableSet (D i) := fun i => (hD₀m i).inter hA
  have hD₀S : ∀ i, D₀ i ⊆ S i := disjointed_subset S
  have hDS : ∀ i, D i ⊆ S i := fun i => Set.inter_subset_left.trans (hD₀S i)
  have hDd : Pairwise (Function.onFun Disjoint D) := fun i j hij =>
    (disjoint_disjointed S hij).mono Set.inter_subset_left Set.inter_subset_left
  have hU₀ : ⋃ i, D₀ i = ⋃ i, S i := iUnion_disjointed
  have hUC₀ : ⋃ i, S i ⊆ coneSet h J := Set.iUnion_subset fun i => (hpc i).2.2.1
  have hUC : ⋃ i, D i ⊆ coneSet h J ∩ A := Set.iUnion_subset fun i y hy =>
    ⟨hUC₀ (hU₀ ▸ Set.mem_iUnion.2 ⟨i, hy.1⟩), hy.2⟩
  have hN : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) ((coneSet h J ∩ A) \ ⋃ i, D i) = 0 := by
    refine measure_mono_null ?_ hnull
    rintro y ⟨⟨hyC, hyA⟩, hyD⟩
    refine ⟨hyC, fun hyS => hyD ?_⟩
    rw [← hU₀] at hyS
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyS
    exact Set.mem_iUnion.2 ⟨i, hi, hyA⟩
  have hCae : (coneSet h J ∩ A : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)] ⋃ i, D i :=
    ae_eq_set.2 ⟨hN, by rw [Set.sdiff_eq_empty.2 hUC]; exact measure_empty⟩
  have hpiece := fun i => hArea m (n - m) n (e i) (Ω i) (Φ i) (hpc i).1 (hpc i).2.1 (D i) (hDS i)
    (hDm i) (coneTangent h J) (fun x hx _ => (hpc i).2.2.2 x hx) π
  have hcount : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      cntOver (coneSet h J ∩ A) π w * g w =
        ∑' i, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_linProj_image_null π hN)] with w hw
    rw [ENNReal.tsum_mul_right, cntOver, ptsOver, ← encard_iUnion_disjoint_nat]
    · congr 3
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hy, rfl⟩
        by_contra hne
        exact hw ⟨y, ⟨hy, fun hyD => hne (by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyD
          exact ⟨i, hi, rfl⟩)⟩, rfl⟩
      · rintro ⟨i, hi, hw'⟩
        exact ⟨hUC (Set.mem_iUnion.2 ⟨i, hi⟩), hw'⟩
    · intro i j hij
      exact (hDd hij).mono (fun y hy => hy.1) (fun y hy => hy.1)
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J ∩ A, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
          ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))
      = ∑' i, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in D i, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
        rw [Measure.restrict_congr_set hCae, lintegral_iUnion hDm hDd, ENNReal.tsum_mul_left]
    _ = ∑' i, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w :=
        tsum_congr fun i => (hpiece i).2 g hg
    _ = Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, cntOver (coneSet h J ∩ A) π w * g w := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum
          (f := fun i w => (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w)
          fun i => (hpiece i).1.mul hg.aemeasurable, lintegral_congr_ae hcount]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
