import Mathlib
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.MeasureBump

/- English proof (translation)
Establish `hmU : m U ≠ 0`. Introduce `h0`. Apply `hm` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero]`. Establish `huniv : (Set.univ : Set X) = U ∪ Uᶜ` using `(Set.union_compl_self U).symm`.

Rewrite using `[huniv]`. Conclude with `measure_union_null h0 hc`. Use `haveI : LocallyCompactSpace U := hU.locallyCompactSpace`. Establish `hσ : IsSigmaCompact U` using `isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance`. Take `⟨K, hK, hKU⟩` from `hσ`.

Establish `hex : ∃ n, m (K n) ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hmU` to reduce the goal to its premises. Rewrite using `[← hKU]`.

Conclude with `measure_iUnion_null hcon`. Take `⟨n, hn⟩` from `hex`. Establish `hsub : K n ⊆ U` using `hKU ▸ Set.subset_iUnion K n`. Take `⟨f, hf1, hfc, hfU, hf01⟩` from `exists_continuousMap_one_of_isCompact_subset_isOpen (hK n) hU hsub`. Use `⟨f, f.continuous, hfc, hfU, ?_⟩` and prove the remaining obligations.

Establish `hI : Integrable (f : X → ℝ) m` using `hint f f.continuous hfc hfU`. Establish `hnn : 0 ≤ᵐ[m] (f : X → ℝ)` using `Filter.Eventually.of_forall fun x => (hf01 x).1`. Establish `hpos : 0 < ∫ x, f x ∂m`. Rewrite using `[integral_pos_iff_support_of_nonneg_ae hnn hI]`. Use `lt_of_lt_of_le (pos_iff_ne_zero.2 hn) (measure_mono ?_)` and prove the remaining obligations.

Introduce `x hx`. Simplify using `[Function.mem_support, hf1 hx]`. Conclude with `hpos.ne'`.
-/
theorem exists_integral_ne_zero_of_carried_by_isOpen
    (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) (U : Set X)
    (hU : IsOpen U) (hc : m Uᶜ = 0) (hm : m ≠ 0)
    (hint : ∀ χ : X → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ U → Integrable χ m) :
    ∃ χ : X → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∫ x, χ x ∂m ≠ 0 := by
  have hmU : m U ≠ 0 := by
    intro h0
    apply hm
    rw [← Measure.measure_univ_eq_zero]
    have huniv : (Set.univ : Set X) = U ∪ Uᶜ := (Set.union_compl_self U).symm
    rw [huniv]
    exact measure_union_null h0 hc
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hK, hKU⟩ := hσ
  have hex : ∃ n, m (K n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hmU
    rw [← hKU]
    exact measure_iUnion_null hcon
  obtain ⟨n, hn⟩ := hex
  have hsub : K n ⊆ U := hKU ▸ Set.subset_iUnion K n
  obtain ⟨f, hf1, hfc, hfU, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK n) hU hsub
  refine ⟨f, f.continuous, hfc, hfU, ?_⟩
  have hI : Integrable (f : X → ℝ) m := hint f f.continuous hfc hfU
  have hnn : 0 ≤ᵐ[m] (f : X → ℝ) := Filter.Eventually.of_forall fun x => (hf01 x).1
  have hpos : 0 < ∫ x, f x ∂m := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hI]
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 hn) (measure_mono ?_)
    intro x hx
    simp [Function.mem_support, hf1 hx]
  exact hpos.ne'

end GlobalTheory.CompanionTheory.MeasureBump
