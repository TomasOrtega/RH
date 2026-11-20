import Mathlib

noncomputable section

namespace MassDataLevelSSteps

open MeasureTheory

/- English proof (translation)
Establish `hrel : H.relIndex K = (H.subgroupOf K).index` using `rfl`. Establish `hAK : ∀ k : K, (fun x => ((k : G))⁻¹ * x) ⁻¹' (H : Set G) ⊆ K`. Introduce `k y hy`. Establish `hy' : ((k : G))⁻¹ * y ∈ K` using `hle hy`. Establish `h2` using `K.mul_mem k.2 hy'`.

Simplify using `using h2`. Establish `hAdisj : ∀ k k' : K, (QuotientGroup.mk k : K ⧸ H.subgroupOf K) ≠ QuotientGroup.mk k' → Disjoint ((fun x => ((k : G))⁻¹ * x) ⁻¹' (H : Set G)) ((fun x => ((k' : G))⁻¹ * x) ⁻¹' (H : Set G))`. Introduce `k k' hne`. Rewrite using `[Set.disjoint_left]`. Introduce `y h1 h2`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Establish `h1' : ((k : G))⁻¹ * y ∈ H` using `h1`. Establish `h2' : ((k' : G))⁻¹ * y ∈ H` using `h2`. Establish `h3` using `H.mul_mem h1' (H.inv_mem h2')`.

Simplify `h3` using `[mul_assoc]`. Break down `Nat.eq_zero_or_pos (H.relIndex K) with h0 | hpos'` into its components or cases. Rewrite using `[h0, Nat.cast_zero, zero_mul]`. Establish `hinf : Infinite (K ⧸ H.subgroupOf K)` using `Subgroup.index_eq_zero_iff_infinite.mp (hrel ▸ h0)`. Set `f : ℕ ↪ K ⧸ H.subgroupOf K` to `Infinite.natEmbedding _`.

Establish `hU` using `measure_iUnion (μ := μ) (f := fun n => (fun x => (((f n).out : K) : G)⁻¹ * x) ⁻¹' (H : Set G)) (fun n m hnm => hAdisj _ _ (by`. Rewrite using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Conclude with `fun h => hnm (f.injective h)))`. Use the proof step `(fun n => (measurable_const_mul _) hH)`. Simplify using `only [measure_preimage_mul, ENNReal.tsum_const_eq_top_of_ne_zero hpos] at hU`.

Establish `htop : μ K = ⊤` using `top_unique (hU ▸ measure_mono (Set.iUnion_subset fun n => hAK _))`. Rewrite using `[htop, ENNReal.toReal_top]`. Establish `hfin : Finite (K ⧸ H.subgroupOf K)` using `Subgroup.index_ne_zero_iff_finite.mp (hrel ▸ hpos'.ne') haveI := Fintype.ofFinite (K ⧸ H.subgroupOf K)`. Establish `hU : (K : Set G) = ⋃ q : K ⧸ H.subgroupOf K, (fun x => ((q.out : K) : G)⁻¹ * x) ⁻¹' (H : Set G)`. Apply `Set.Subset.antisymm` to reduce the goal to its premises.

Introduce `y hy`. Use `Set.mem_iUnion.mpr ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨y, hy⟩ : K ⧸ H.subgroupOf K))`. Rewrite `h1` using `[Subgroup.mem_subgroupOf]`. Use `show _ ∈ H`.

Simplify using `using h1`. Conclude with `Set.iUnion_subset fun q => hAK _`. Establish `hμK : μ K = ∑ q : K ⧸ H.subgroupOf K, μ H`. Rewrite using `[hU, measure_iUnion (fun q q' hqq => hAdisj _ _ (by`. Rewrite using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`.

Conclude with `hqq)) (fun q => (measurable_const_mul _) hH), tsum_fintype]`. Conclude with `Finset.sum_congr rfl fun q _ => measure_preimage_mul μ _ _`. Establish `hc : (H.relIndex K : ℝ) = (Fintype.card (K ⧸ H.subgroupOf K) : ℝ)`. Rewrite using `[hrel, Subgroup.index, Nat.card_eq_fintype_card]`. Rewrite using `[hμK, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, hc]`.
-/
theorem toReal_eq_relIndex_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H K : Subgroup G) (hle : H ≤ K)
    (hK : MeasurableSet (K : Set G)) (hH : MeasurableSet (H : Set G)) (hpos : μ H ≠ 0) :
    (μ K).toReal = (H.relIndex K : ℝ) * (μ H).toReal := by
  classical
  have hrel : H.relIndex K = (H.subgroupOf K).index := rfl
  have hAK : ∀ k : K, (fun x => ((k : G))⁻¹ * x) ⁻¹' (H : Set G) ⊆ K := by
    intro k y hy
    have hy' : ((k : G))⁻¹ * y ∈ K := hle hy
    have h2 := K.mul_mem k.2 hy'
    simpa using h2
  have hAdisj : ∀ k k' : K, (QuotientGroup.mk k : K ⧸ H.subgroupOf K) ≠ QuotientGroup.mk k' →
      Disjoint ((fun x => ((k : G))⁻¹ * x) ⁻¹' (H : Set G))
        ((fun x => ((k' : G))⁻¹ * x) ⁻¹' (H : Set G)) := by
    intro k k' hne
    rw [Set.disjoint_left]
    intro y h1 h2
    apply hne
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1' : ((k : G))⁻¹ * y ∈ H := h1
    have h2' : ((k' : G))⁻¹ * y ∈ H := h2
    have h3 := H.mul_mem h1' (H.inv_mem h2')
    simpa [mul_assoc] using h3
  rcases Nat.eq_zero_or_pos (H.relIndex K) with h0 | hpos'
  · rw [h0, Nat.cast_zero, zero_mul]
    have hinf : Infinite (K ⧸ H.subgroupOf K) :=
      Subgroup.index_eq_zero_iff_infinite.mp (hrel ▸ h0)
    let f : ℕ ↪ K ⧸ H.subgroupOf K := Infinite.natEmbedding _
    have hU := measure_iUnion (μ := μ)
      (f := fun n => (fun x => (((f n).out : K) : G)⁻¹ * x) ⁻¹' (H : Set G))
      (fun n m hnm => hAdisj _ _ (by
        rw [QuotientGroup.out_eq', QuotientGroup.out_eq']
        exact fun h => hnm (f.injective h)))
      (fun n => (measurable_const_mul _) hH)
    simp only [measure_preimage_mul, ENNReal.tsum_const_eq_top_of_ne_zero hpos] at hU
    have htop : μ K = ⊤ := top_unique (hU ▸ measure_mono (Set.iUnion_subset fun n => hAK _))
    rw [htop, ENNReal.toReal_top]
  · have hfin : Finite (K ⧸ H.subgroupOf K) :=
      Subgroup.index_ne_zero_iff_finite.mp (hrel ▸ hpos'.ne')
    haveI := Fintype.ofFinite (K ⧸ H.subgroupOf K)
    have hU : (K : Set G) = ⋃ q : K ⧸ H.subgroupOf K,
        (fun x => ((q.out : K) : G)⁻¹ * x) ⁻¹' (H : Set G) := by
      apply Set.Subset.antisymm
      · intro y hy
        refine Set.mem_iUnion.mpr ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩
        have h1 := QuotientGroup.eq.mp
          (QuotientGroup.out_eq' (QuotientGroup.mk ⟨y, hy⟩ : K ⧸ H.subgroupOf K))
        rw [Subgroup.mem_subgroupOf] at h1
        show _ ∈ H
        simpa using h1
      · exact Set.iUnion_subset fun q => hAK _
    have hμK : μ K = ∑ q : K ⧸ H.subgroupOf K, μ H := by
      rw [hU, measure_iUnion (fun q q' hqq => hAdisj _ _ (by
          rw [QuotientGroup.out_eq', QuotientGroup.out_eq']
          exact hqq)) (fun q => (measurable_const_mul _) hH), tsum_fintype]
      exact Finset.sum_congr rfl fun q _ => measure_preimage_mul μ _ _
    have hc : (H.relIndex K : ℝ) = (Fintype.card (K ⧸ H.subgroupOf K) : ℝ) := by
      rw [hrel, Subgroup.index, Nat.card_eq_fintype_card]
    rw [hμK, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, hc]

/- English proof (translation)
Establish `hK : IsOpen (K : Set G)` using `Subgroup.isOpen_mono hle hH`. Conclude with `toReal_eq_relIndex_mul μ H K hle hK.measurableSet hH.measurableSet (hH.measure_ne_zero μ ⟨1, H.one_mem⟩)`.
-/
theorem toReal_eq_relIndex_mul_of_open {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    (H K : Subgroup G) (hle : H ≤ K) (hH : IsOpen (H : Set G)) :
    (μ K).toReal = (H.relIndex K : ℝ) * (μ H).toReal := by
  have hK : IsOpen (K : Set G) := Subgroup.isOpen_mono hle hH
  exact toReal_eq_relIndex_mul μ H K hle hK.measurableSet hH.measurableSet
    (hH.measure_ne_zero μ ⟨1, H.one_mem⟩)

/- English proof (translation)
Use `haveI := hc`. Use `haveI := hB`. Use `haveI := hμ`. Conclude with `toReal_eq_relIndex_mul_of_open μ H K hle hH`.
-/
theorem toReal_eq_relIndex_mul_of_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (hc : ContinuousMul G) (hB : BorelSpace G) (μ : Measure G) (hμ : μ.IsHaarMeasure)
    (H K : Subgroup G) (hle : H ≤ K) (hH : IsOpen (H : Set G)) :
    (μ K).toReal = (H.relIndex K : ℝ) * (μ H).toReal := by
  haveI := hc
  haveI := hB
  haveI := hμ
  exact toReal_eq_relIndex_mul_of_open μ H K hle hH

end MassDataLevelSSteps
