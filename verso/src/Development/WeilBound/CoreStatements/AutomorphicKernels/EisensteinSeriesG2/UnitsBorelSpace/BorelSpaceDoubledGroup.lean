import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2

noncomputable section

namespace GlobalTheory.EisBL.Borel

open Topology MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

/- English proof (translation)
Establish `hce` using `Units.isClosedEmbedding_embedProduct (α := M)`. Use `haveI : LocallyCompactSpace Mˣ := hce.locallyCompactSpace`. Use `haveI : SecondCountableTopology Mᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology`. Use `haveI : SecondCountableTopology Mˣ := hce.isEmbedding.secondCountableTopology`. Use `⟨le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Use `show MeasurableSpace.comap Units.val ‹MeasurableSpace M› ≤ borel Mˣ`. Rewrite using `[BorelSpace.measurable_eq (α := M)]`. Rewrite using `[← @borel_comap Mˣ M Units.val _]`. Conclude with `borel_anti (continuous_iff_le_induced.mp Units.continuous_val)`. Rewrite using `[borel_eq_generateFrom_isClosed]`.

Use `MeasurableSpace.generateFrom_le fun C hC => ?_` and prove the remaining obligations. Establish `key : C = Units.val ⁻¹' (⋃ n, Units.val '' (C ∩ compactCovering Mˣ n))`. Use extensionality with `u`. Simplify using `only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce `hu`. Establish `hmem : u ∈ ⋃ n, compactCovering Mˣ n`. Rewrite using `[iUnion_compactCovering]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨n, hn⟩` from `Set.mem_iUnion.mp hmem`.

Conclude with `⟨n, u, ⟨hu, hn⟩, rfl⟩`. Introduce and unpack `⟨n, v, ⟨hv, _⟩, hvu⟩`. Rewrite using `[← Units.ext hvu]` and apply the resulting hypothesis. Rewrite using `[key]`. Use `⟨_, MeasurableSet.iUnion fun n => ?_, rfl⟩` and prove the remaining obligations.

Conclude with `(((isCompact_compactCovering Mˣ n).inter_left hC).image Units.continuous_val).isClosed.measurableSet`.
-/
theorem units_borelSpace (M : Type*) [Monoid M] [TopologicalSpace M] [T2Space M] [ContinuousMul M]
    [LocallyCompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    BorelSpace Mˣ := by
  have hce := Units.isClosedEmbedding_embedProduct (α := M)
  haveI : LocallyCompactSpace Mˣ := hce.locallyCompactSpace
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology Mˣ := hce.isEmbedding.secondCountableTopology
  refine ⟨le_antisymm ?_ ?_⟩
  · show MeasurableSpace.comap Units.val ‹MeasurableSpace M› ≤ borel Mˣ
    rw [BorelSpace.measurable_eq (α := M)]
    rw [← @borel_comap Mˣ M Units.val _]
    exact borel_anti (continuous_iff_le_induced.mp Units.continuous_val)
  · rw [borel_eq_generateFrom_isClosed]
    refine MeasurableSpace.generateFrom_le fun C hC => ?_
    have key : C = Units.val ⁻¹' (⋃ n, Units.val '' (C ∩ compactCovering Mˣ n)) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
      constructor
      · intro hu
        have hmem : u ∈ ⋃ n, compactCovering Mˣ n := by
          rw [iUnion_compactCovering]
          trivial
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
        exact ⟨n, u, ⟨hu, hn⟩, rfl⟩
      · rintro ⟨n, v, ⟨hv, _⟩, hvu⟩
        rwa [← Units.ext hvu]
    rw [key]
    refine ⟨_, MeasurableSet.iUnion fun n => ?_, rfl⟩
    exact (((isCompact_compactCovering Mˣ n).inter_left hC).image Units.continuous_val).isClosed.measurableSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance borelAE : BorelSpace (AE F E) := ⟨rfl⟩

instance borelMatAE {ι : Type} [Fintype ι] : BorelSpace (Matrix ι ι (AE F E)) :=
  inferInstanceAs (BorelSpace (ι → ι → AE F E))

instance borelGL {ι : Type} [Fintype ι] [DecidableEq ι] : BorelSpace (GL ι (AE F E)) := by
  have : LocallyCompactSpace (Matrix ι ι (AE F E)) := inferInstanceAs (LocallyCompactSpace (ι → ι → AE F E))
  have : SecondCountableTopology (Matrix ι ι (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → AE F E))
  exact units_borelSpace _

instance borelSpace_doubled_group {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} : BorelSpace (G2 σ Y) := Subtype.borelSpace _

end GlobalTheory.EisBL.Borel
