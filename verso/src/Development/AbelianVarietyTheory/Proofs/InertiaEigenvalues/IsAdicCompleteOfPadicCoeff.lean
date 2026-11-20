import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨L, hL⟩` from `exists_clusterPt_of_compactSpace (Filter.map f Filter.atTop)`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `hopen : IsOpen ((I ^ n : Ideal O) : Set O)` using `(isAdic_iff.mp h).1 n`. Establish `hclosed : IsClosed ((I ^ n : Ideal O) : Set O)` using `AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup hopen`.

Establish `hc : IsClosed {x : O | f n - x ∈ I ^ n}` using `hclosed.preimage (f := fun x => f n - x) (continuous_const.sub continuous_id)`. Establish `hmem : {x : O | f n - x ∈ I ^ n} ∈ Filter.map f Filter.atTop`. Rewrite using `[Filter.mem_map]`. Use `filter_upwards [Filter.eventually_ge_atTop n] with k hk`. Use `hf hk` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Conclude with `this`. Establish `hLm : L ∈ {x : O | f n - x ∈ I ^ n}`. Rewrite using `[← hc.closure_eq]`. Conclude with `mem_closure_iff_clusterPt.mpr (hL.mono (Filter.le_principal_iff.mpr hmem))`.

Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Conclude with `hLm`.
-/
theorem isPrecomplete_of_compact_isAdic {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (h : IsAdic I) : IsPrecomplete I O := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := exists_clusterPt_of_compactSpace (Filter.map f Filter.atTop)
  refine ⟨L, fun n => ?_⟩
  have hopen : IsOpen ((I ^ n : Ideal O) : Set O) := (isAdic_iff.mp h).1 n
  have hclosed : IsClosed ((I ^ n : Ideal O) : Set O) :=
    AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup hopen
  have hc : IsClosed {x : O | f n - x ∈ I ^ n} :=
    hclosed.preimage (f := fun x => f n - x) (continuous_const.sub continuous_id)
  have hmem : {x : O | f n - x ∈ I ^ n} ∈ Filter.map f Filter.atTop := by
    rw [Filter.mem_map]
    filter_upwards [Filter.eventually_ge_atTop n] with k hk
    have := hf hk
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  have hLm : L ∈ {x : O | f n - x ∈ I ^ n} := by
    rw [← hc.closure_eq]
    exact mem_closure_iff_clusterPt.mpr (hL.mono (Filter.le_principal_iff.mpr hmem))
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact hLm

/- English proof (translation)
Use `haveI := h.ring`. Use `haveI := h.compact`. Use `haveI := isPrecomplete_of_compact_isAdic _ h.adic`. Use `haveI : IsHausdorff (IsLocalRing.maximalIdeal O) O := inferInstance`. Conclude with `⟨⟩`.
-/
theorem isAdicComplete_of_padicCoeff {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (h : PadicCoeff p O) : IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  haveI := h.ring
  haveI := h.compact
  haveI := isPrecomplete_of_compact_isAdic _ h.adic
  haveI : IsHausdorff (IsLocalRing.maximalIdeal O) O := inferInstance
  exact ⟨⟩

end GlobalTheory
