import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereChartDensityIntegralStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

omit [CompactSpace X] [T2Space X] in

/- English proof (translation)
Establish `h : Q.χ j x ≤ ∑ k, Q.χ k x` using `Finset.single_le_sum (f := fun k => Q.χ k x) (fun k _ => Q.nonneg k x) (Finset.mem_univ j)`. Rewrite `h` using `[Q.sum_eq_one]`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (Q.nonneg j x)]`. Conclude with `h`.
-/
theorem chartPartition_norm_le_one (A : FinHolAtlas e X) (Q : ChartPartition A) (j : Fin A.n)
    (x : X) : ‖Q.χ j x‖ ≤ 1 := by
  have h : Q.χ j x ≤ ∑ k, Q.χ k x :=
    Finset.single_le_sum (f := fun k => Q.χ k x) (fun k _ => Q.nonneg k x) (Finset.mem_univ j)
  rw [Q.sum_eq_one] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (Q.nonneg j x)]
  exact h

/- English proof (translation)
Establish `hK : IsCompact (A.chart j '' tsupport (Q.χ j))` using `(isClosed_tsupport _).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono (Q.tsupport_subset j))`. Establish `hKt : A.chart j '' tsupport (Q.χ j) ⊆ (A.chart j).target`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(A.chart j).map_source (Q.tsupport_subset j hx)`. Establish `h0` using `hg j _ hKt hK`.

Establish `hcont : ContinuousOn (fun y => Q.χ j ((A.chart j).symm y)) (A.chart j).target`. Establish `h` using `(Q.smooth j j).continuousOn`. Simplify `h` using `[Function.comp_def]`. Establish `hm : AEStronglyMeasurable (fun y => Q.χ j ((A.chart j).symm y)) (volume.restrict (A.chart j '' tsupport (Q.χ j)))` using `(hcont.mono hKt).aestronglyMeasurable hK.measurableSet`. Establish `h1 : IntegrableOn (fun y => Q.χ j ((A.chart j).symm y) * (g ((A.chart j).symm y) * locDens A P j y)) (A.chart j '' tsupport (Q.χ j))` using `Integrable.bdd_mul (c := 1) h0 hm (ae_of_all _ fun y => chartPartition_norm_le_one A Q j _)`.

Establish `h2 : IntegrableOn (fun y => Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y) (A.chart j '' tsupport (Q.χ j))`. Simplify `h1` using `only [mul_assoc]`. Use `IntegrableOn.of_forall_sdiff_eq_zero h2 (A.chart j).open_target.measurableSet ?_` and prove the remaining obligations. Introduce and unpack `y ⟨hy, hyK⟩`. Establish `hn : (A.chart j).symm y ∉ tsupport (Q.χ j)` using `fun hmem => hyK ⟨_, hmem, (A.chart j).right_inv hy⟩`.

Rewrite using `[image_eq_zero_of_notMem_tsupport hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chartTerm_integrableOn (A : FinHolAtlas e X) (Q : ChartPartition A) (P : Fin e → LocPot X)
    (g : X → ℝ) (hg : MIntegrable A P g) (j : Fin A.n) :
    IntegrableOn (fun y => Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y)
      (A.chart j).target := by
  have hK : IsCompact (A.chart j '' tsupport (Q.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (Q.tsupport_subset j))
  have hKt : A.chart j '' tsupport (Q.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (Q.tsupport_subset j hx)
  have h0 := hg j _ hKt hK
  have hcont : ContinuousOn (fun y => Q.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have h := (Q.smooth j j).continuousOn
    simpa [Function.comp_def] using h
  have hm : AEStronglyMeasurable (fun y => Q.χ j ((A.chart j).symm y))
      (volume.restrict (A.chart j '' tsupport (Q.χ j))) :=
    (hcont.mono hKt).aestronglyMeasurable hK.measurableSet
  have h1 : IntegrableOn
      (fun y => Q.χ j ((A.chart j).symm y) * (g ((A.chart j).symm y) * locDens A P j y))
      (A.chart j '' tsupport (Q.χ j)) :=
    Integrable.bdd_mul (c := 1) h0 hm (ae_of_all _ fun y => chartPartition_norm_le_one A Q j _)
  have h2 : IntegrableOn
      (fun y => Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y)
      (A.chart j '' tsupport (Q.χ j)) := by
    simpa only [mul_assoc] using h1
  refine IntegrableOn.of_forall_sdiff_eq_zero h2 (A.chart j).open_target.measurableSet ?_
  rintro y ⟨hy, hyK⟩
  have hn : (A.chart j).symm y ∉ tsupport (Q.χ j) := fun hmem =>
    hyK ⟨_, hmem, (A.chart j).right_inv hy⟩
  rw [image_eq_zero_of_notMem_tsupport hn]
  ring

/- English proof (translation)
Take `⟨hpar, hB, hdisj, hnull⟩` from `hc`. Establish `hf` using `chartTerm_integrableOn A Q P g hg j`. Establish `hCm : ∀ n, MeasurableSet (B n ∩ Φ n ⁻¹' (A.chart j).source)`. Introduce `n`. Establish `hO : IsOpen (V n ∩ Φ n ⁻¹' (A.chart j).source)` using `(hpar n).2.1.isOpen_inter_preimage (hpar n).1 (A.chart j).open_source`.

Establish `hEq : B n ∩ Φ n ⁻¹' (A.chart j).source = B n ∩ (V n ∩ Φ n ⁻¹' (A.chart j).source)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, (hB n).2 h1, h2⟩`.

Introduce and unpack `⟨h1, _, h2⟩`. Conclude with `⟨h1, h2⟩`. Rewrite using `[hEq]`. Conclude with `(hB n).1.inter hO.measurableSet`. Establish `key` using `fun n => GlobalTheory.T.monge_ampere_chart_density_integral e X A (V n) (B n ∩ Φ n ⁻¹' (A.chart j).source) (Φ n) P (fun x => Q.χ j x * g x) j (hpar n) (hCm n) (fun z hz => (hB n).2 hz.1) (fun z hz => hz.2) (fun z hz => hC2 n z hz.1)`.

Establish `hsub : ∀ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source) ⊆ (A.chart j).target`. Introduce and unpack `n _ ⟨z, hz, rfl⟩`. Conclude with `(A.chart j).map_source hz.2`. Establish `hzero : ∀ n, ∀ z ∈ B n \ (B n ∩ Φ n ⁻¹' (A.chart j).source), Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z = 0`. Introduce and unpack `n z ⟨hz, hz'⟩`.

Establish `hn : Φ n z ∉ tsupport (Q.χ j)` using `fun hmem => hz' ⟨hz, Q.tsupport_subset j hmem⟩`. Rewrite using `[image_eq_zero_of_notMem_tsupport hn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdis : Pairwise (Function.onFun Disjoint fun n => (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source))`. Introduce `n m hnm`.

Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩`. Establish `hEq : Φ n z = Φ m w`. Use `(A.chart j).injOn hz.2 hw.2 ?_` and prove the remaining obligations. Conclude with `hzw.symm`.

Conclude with `Set.disjoint_left.1 (hdisj hnm) ⟨z, hz.1, rfl⟩ ⟨w, hw.1, hEq.symm⟩`. Establish `hUsub : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) ⊆ (A.chart j).target` using `Set.iUnion_subset hsub`. Establish `hsum` using `hasSum_integral_iUnion (fun n => (key n).1) hdis (hf.mono_set hUsub)`. Establish `hUeq : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) =ᵐ[volume] (A.chart j).target`. Use `ae_eq_set.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.sdiff_eq_empty.2 hUsub]`. Conclude with `measure_empty`. Use `measure_mono_null ?_ (hnull j)` and prove the remaining obligations. Introduce and unpack `y ⟨hy, hyU⟩`. Use `⟨hy, ?_⟩` and prove the remaining obligations.

Introduce `hmem`. Take `⟨_, ⟨n, rfl⟩, z, hz, hzy⟩` from `hmem`. Use `hyU (Set.mem_iUnion.2 ⟨n, z, ⟨hz, ?_⟩, ?_⟩)` and prove the remaining obligations. Use `show Φ n z ∈ (A.chart j).source`. Rewrite using `[hzy]`.

Conclude with `(A.chart j).map_target hy`. Use `show A.chart j (Φ n z) = y`. Rewrite using `[hzy]`. Conclude with `(A.chart j).right_inv hy`. Rewrite `hsum` using `[setIntegral_congr_set hUeq]`.

Prove the components needed by the constructor for the conclusion. Introduce `n`. Use `IntegrableOn.of_forall_sdiff_eq_zero ((key n).2.1.1 (hf.mono_set (hsub n))) (hB n).1 (hzero n)` and prove the remaining obligations. Establish `hEq : (fun n => ∫ z in B n, Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z) = fun n => ∫ y in (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source), Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y`. Use function extensionality and compare the values at `n`.

Rewrite using `[setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hB n).1 Set.inter_subset_left (hzero n)]`. Conclude with `((key n).2.2).symm`. Rewrite using `[hEq]`. Conclude with `hsum`.
-/
theorem chartTerm_hasSum (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ))
    (Φ : ℕ → (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (Q : ChartPartition A)
    (hc : IsParamCover A V B Φ) (hC2 : ∀ n, ∀ z ∈ B n, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ n z))
    (hg : MIntegrable A P g) (j : Fin A.n) :
    (∀ n, IntegrableOn (fun z => Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z) (B n)) ∧
      HasSum (fun n => ∫ z in B n, Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z)
        (∫ y in (A.chart j).target,
          Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y) := by
  obtain ⟨hpar, hB, hdisj, hnull⟩ := hc
  have hf := chartTerm_integrableOn A Q P g hg j
  have hCm : ∀ n, MeasurableSet (B n ∩ Φ n ⁻¹' (A.chart j).source) := by
    intro n
    have hO : IsOpen (V n ∩ Φ n ⁻¹' (A.chart j).source) :=
      (hpar n).2.1.isOpen_inter_preimage (hpar n).1 (A.chart j).open_source
    have hEq : B n ∩ Φ n ⁻¹' (A.chart j).source = B n ∩ (V n ∩ Φ n ⁻¹' (A.chart j).source) := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hB n).2 h1, h2⟩
      · rintro ⟨h1, _, h2⟩
        exact ⟨h1, h2⟩
    rw [hEq]
    exact (hB n).1.inter hO.measurableSet
  have key := fun n => GlobalTheory.T.monge_ampere_chart_density_integral e X A (V n) (B n ∩ Φ n ⁻¹' (A.chart j).source) (Φ n) P
    (fun x => Q.χ j x * g x) j (hpar n) (hCm n) (fun z hz => (hB n).2 hz.1) (fun z hz => hz.2)
    (fun z hz => hC2 n z hz.1)
  have hsub : ∀ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source) ⊆
      (A.chart j).target := by
    rintro n _ ⟨z, hz, rfl⟩
    exact (A.chart j).map_source hz.2
  have hzero : ∀ n, ∀ z ∈ B n \ (B n ∩ Φ n ⁻¹' (A.chart j).source),
      Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z = 0 := by
    rintro n z ⟨hz, hz'⟩
    have hn : Φ n z ∉ tsupport (Q.χ j) := fun hmem =>
      hz' ⟨hz, Q.tsupport_subset j hmem⟩
    rw [image_eq_zero_of_notMem_tsupport hn]
    ring
  have hdis : Pairwise (Function.onFun Disjoint fun n =>
      (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩
    have hEq : Φ n z = Φ m w := by
      refine (A.chart j).injOn hz.2 hw.2 ?_
      exact hzw.symm
    exact Set.disjoint_left.1 (hdisj hnm) ⟨z, hz.1, rfl⟩ ⟨w, hw.1, hEq.symm⟩
  have hUsub : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) ⊆
      (A.chart j).target := Set.iUnion_subset hsub
  have hsum := hasSum_integral_iUnion (fun n => (key n).1) hdis (hf.mono_set hUsub)
  have hUeq : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) =ᵐ[volume]
      (A.chart j).target := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.2 hUsub]
      exact measure_empty
    · refine measure_mono_null ?_ (hnull j)
      rintro y ⟨hy, hyU⟩
      refine ⟨hy, ?_⟩
      intro hmem
      obtain ⟨_, ⟨n, rfl⟩, z, hz, hzy⟩ := hmem
      refine hyU (Set.mem_iUnion.2 ⟨n, z, ⟨hz, ?_⟩, ?_⟩)
      · show Φ n z ∈ (A.chart j).source
        rw [hzy]
        exact (A.chart j).map_target hy
      · show A.chart j (Φ n z) = y
        rw [hzy]
        exact (A.chart j).right_inv hy
  rw [setIntegral_congr_set hUeq] at hsum
  constructor
  · intro n
    refine IntegrableOn.of_forall_sdiff_eq_zero
      ((key n).2.1.1 (hf.mono_set (hsub n))) (hB n).1 (hzero n)
  · have hEq : (fun n => ∫ z in B n, Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z) =
        fun n => ∫ y in (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source),
          Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y := by
      funext n
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hB n).1 Set.inter_subset_left
        (hzero n)]
      exact ((key n).2.2).symm
    rw [hEq]
    exact hsum

/- English proof (translation)
Introduce `e X _ _ _ A V B Φ P g hc hC2 hg`. Establish `hne : Nonempty (ChartPartition A)` using `existsPartition A`. Establish `hm : mInt A P g = ∑ j, ∫ y in (A.chart j).target, hne.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y`. Rewrite using `[mInt, dif_pos hne, integralWith]`. Establish `hj` using `fun j => chartTerm_hasSum A V B Φ P g hne.some hc hC2 hg j`.

Establish `hpt : ∀ n z, g (Φ n z) * paramDens P (Φ n) z = ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z`. Introduce `n z`. Rewrite using `[← Finset.sum_mul, ← Finset.sum_mul, hne.some.sum_eq_one, one_mul]`. Establish `hfun : ∀ n, (fun z => g (Φ n z) * paramDens P (Φ n) z) = fun z => ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z` using `fun n => funext (hpt n)`. Prove the components needed by the constructor for the conclusion.

Introduce `n`. Rewrite using `[hfun n]`. Conclude with `integrable_finsetSum _ fun j _ => (hj j).1 n`. Rewrite using `[hm]`. Establish `hs` using `hasSum_sum (s := Finset.univ) fun j _ => (hj j).2`.

Establish `hEq : (fun n => ∫ z in B n, g (Φ n z) * paramDens P (Φ n) z) = fun n => ∑ j, ∫ z in B n, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z`. Use function extensionality and compare the values at `n`. Rewrite using `[hfun n]`. Conclude with `integral_finset_sum _ fun j _ => (hj j).1 n`. Rewrite using `[hEq]`.

Conclude with `hs`.
-/
theorem integrableOn_hasSum_paramCover : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ)) (Φ : ℕ → (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ), IsParamCover A V B Φ → (∀ n, ∀ z ∈ B n, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ n z)) → MIntegrable A P g → (∀ n, IntegrableOn (fun z => g (Φ n z) * paramDens P (Φ n) z) (B n)) ∧ HasSum (fun n => ∫ z in B n, g (Φ n z) * paramDens P (Φ n) z) (mInt A P g) := by
  intro e X _ _ _ A V B Φ P g hc hC2 hg
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hm : mInt A P g = ∑ j, ∫ y in (A.chart j).target,
      hne.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y := by
    rw [mInt, dif_pos hne, integralWith]
  have hj := fun j => chartTerm_hasSum A V B Φ P g hne.some hc hC2 hg j
  have hpt : ∀ n z, g (Φ n z) * paramDens P (Φ n) z =
      ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z := by
    intro n z
    rw [← Finset.sum_mul, ← Finset.sum_mul, hne.some.sum_eq_one, one_mul]
  have hfun : ∀ n, (fun z => g (Φ n z) * paramDens P (Φ n) z) =
      fun z => ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z :=
    fun n => funext (hpt n)
  constructor
  · intro n
    rw [hfun n]
    exact integrable_finsetSum _ fun j _ => (hj j).1 n
  · rw [hm]
    have hs := hasSum_sum (s := Finset.univ) fun j _ => (hj j).2
    have hEq : (fun n => ∫ z in B n, g (Φ n z) * paramDens P (Φ n) z) =
        fun n => ∑ j, ∫ z in B n, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z := by
      funext n
      rw [hfun n]
      exact integral_finset_sum _ fun j _ => (hj j).1 n
    rw [hEq]
    exact hs

end

end GlobalTheory.CompanionTheory.Ar.PB
