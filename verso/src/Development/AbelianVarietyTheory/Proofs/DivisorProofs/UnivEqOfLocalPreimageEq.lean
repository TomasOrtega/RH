import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

/- English proof (translation)
Introduce `M N _ _ _ _ _ π hπ μ ν h`. Use `choose U hUo hxU hU using h`. Take `⟨S, hSc, hS⟩` from `TopologicalSpace.isOpen_iUnion_countable U hUo`. Use `haveI : Countable S := hSc.to_subtype`. Establish `hcov : ⋃ i : S, U i = Set.univ`.

Rewrite using `[← Set.biUnion_eq_iUnion S (fun i _ => U i), hS]`. Conclude with `Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hxU x⟩`. Establish `hmap : μ.map π = ν`. Use `(Measure.ext_iff_of_iUnion_eq_univ hcov).2 fun i => ?_` and prove the remaining obligations. Use extensionality with `T hT`.

Establish `hm : MeasurableSet (T ∩ U i)` using `hT.inter (hUo i).measurableSet`. Rewrite using `[Measure.restrict_apply hT, Measure.restrict_apply hT, Measure.map_apply hπ hm]`. Conclude with `hU i _ hm Set.inter_subset_right`. Establish `: μ Set.univ = μ.map π Set.univ`. Rewrite using `[Measure.map_apply hπ MeasurableSet.univ, Set.preimage_univ]`.

Rewrite using `[this, hmap]`.
-/
theorem GlobalTheory.FlagCell2.univ_eq_of_local_preimage_eq : ∀ (M N : Type) [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] (π : N → M), Measurable π → ∀ (μ : Measure N) (ν : Measure M), (∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ T, MeasurableSet T → T ⊆ U → μ (π ⁻¹' T) = ν T) → μ Set.univ = ν Set.univ := by
  intro M N _ _ _ _ _ π hπ μ ν h
  choose U hUo hxU hU using h
  obtain ⟨S, hSc, hS⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  haveI : Countable S := hSc.to_subtype
  have hcov : ⋃ i : S, U i = Set.univ := by
    rw [← Set.biUnion_eq_iUnion S (fun i _ => U i), hS]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hxU x⟩
  have hmap : μ.map π = ν := by
    refine (Measure.ext_iff_of_iUnion_eq_univ hcov).2 fun i => ?_
    ext T hT
    have hm : MeasurableSet (T ∩ U i) := hT.inter (hUo i).measurableSet
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT, Measure.map_apply hπ hm]
    exact hU i _ hm Set.inter_subset_right
  have : μ Set.univ = μ.map π Set.univ := by
    rw [Measure.map_apply hπ MeasurableSet.univ, Set.preimage_univ]
  rw [this, hmap]
