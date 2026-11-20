import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitHomeoApply
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

/- English proof (translation)
Introduce `P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ _ hU hK`. Take `⟨U, hU, hU1⟩` from `hU`. Take `⟨K, hKc, hK⟩` from `hK`. Establish `hcl : IsClosed (π.ker : Set P)`. Establish `: (π.ker : Set P) = π ⁻¹' {1}`.

Use extensionality with `x`. Simplify using `[MonoidHom.mem_ker]`. Rewrite using `[this]`. Conclude with `isClosed_singleton.preimage hπ`. Establish `hemb : IsClosedEmbedding (Subtype.val : π.ker → P)` using `hcl.isClosedEmbedding_subtypeVal`.

Use `haveI : LocallyCompactSpace π.ker := hemb.locallyCompactSpace`. Use `haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : BorelSpace π.ker := Subtype.borelSpace _`. Use `haveI : Countable (Γ.subgroupOf π.ker) := Function.Injective.countable (f := fun h : Γ.subgroupOf π.ker => (⟨((h : π.ker) : P), h.2⟩ : Γ)) (fun a b hab => by`. Establish `h1 : ((a : π.ker) : P) = ((b : π.ker) : P)` using `congrArg (fun x : Γ => (x : P)) hab`.

Conclude with `Subtype.ext (Subtype.ext h1))`. Use `haveI : DiscreteTopology (Γ.subgroupOf π.ker) := by`. Use `discreteTopology_of_isOpen_singleton_one ?_` and prove the remaining obligations. Establish `hc : Continuous fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P)` using `continuous_subtype_val.comp continuous_subtype_val`. Establish `: ({1} : Set (Γ.subgroupOf π.ker)) = (fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P)) ⁻¹' interior U`.

Use extensionality with `h`. Simplify using `only [Set.mem_singleton_iff, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `mem_interior_iff_mem_nhds.2 hU`.

Introduce `hh`. Establish `h1 : ((h : π.ker) : P) = 1` using `hU1 _ (Subgroup.mem_subgroupOf.1 h.2) (interior_subset hh)`. Conclude with `Subtype.ext (Subtype.ext h1)`. Rewrite using `[this]`. Conclude with `isOpen_interior.preimage hc`.

Take `⟨D, hDm, hDu, hDf⟩` from `GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf π.ker)`. Use `⟨D, hDm, hDu, fun ν _ => ⟨hDf ν, (hDf ν).measure_ne_zero (NeZero.ne ν), ?_⟩⟩` and prove the remaining obligations. Establish `hKc' : IsCompact ((Subtype.val : π.ker → P) ⁻¹' K)` using `hemb.isCompact_preimage hKc`. Use `lt_of_le_of_lt (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hDf ν) (D' := (Subtype.val : π.ker → P) ⁻¹' K) (.of_forall fun m => ?_)) hKc'.measure_lt_top` and prove the remaining obligations. Take `⟨γ, hγ, hπγ, hmem⟩` from `hK m m.2`.

Establish `hγk : γ ∈ π.ker` using `hπγ`. Use `⟨⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 hγ⟩, ?_⟩` and prove the remaining obligations. Conclude with `hmem`.
-/
theorem exists_borel_section_ker :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) [Countable Γ], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ D : Set π.ker, MeasurableSet D ∧ (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) ∧ ∀ (ν : Measure π.ker) [ν.IsHaarMeasure], IsFundamentalDomain (Γ.subgroupOf π.ker) D ν ∧ ν D ≠ 0 ∧ ν D < ⊤ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ _ hU hK
  obtain ⟨U, hU, hU1⟩ := hU
  obtain ⟨K, hKc, hK⟩ := hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hπ
  have hemb : IsClosedEmbedding (Subtype.val : π.ker → P) := hcl.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace π.ker := hemb.locallyCompactSpace
  haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace π.ker := Subtype.borelSpace _
  haveI : Countable (Γ.subgroupOf π.ker) :=
    Function.Injective.countable (f := fun h : Γ.subgroupOf π.ker =>
      (⟨((h : π.ker) : P), h.2⟩ : Γ)) (fun a b hab => by
        have h1 : ((a : π.ker) : P) = ((b : π.ker) : P) := congrArg (fun x : Γ => (x : P)) hab
        exact Subtype.ext (Subtype.ext h1))
  haveI : DiscreteTopology (Γ.subgroupOf π.ker) := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hc : Continuous fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P) :=
      continuous_subtype_val.comp continuous_subtype_val
    have : ({1} : Set (Γ.subgroupOf π.ker)) =
        (fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P)) ⁻¹' interior U := by
      ext h
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        exact mem_interior_iff_mem_nhds.2 hU
      · intro hh
        have h1 : ((h : π.ker) : P) = 1 :=
          hU1 _ (Subgroup.mem_subgroupOf.1 h.2) (interior_subset hh)
        exact Subtype.ext (Subtype.ext h1)
    rw [this]
    exact isOpen_interior.preimage hc
  obtain ⟨D, hDm, hDu, hDf⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf π.ker)
  refine ⟨D, hDm, hDu, fun ν _ => ⟨hDf ν, (hDf ν).measure_ne_zero (NeZero.ne ν), ?_⟩⟩
  have hKc' : IsCompact ((Subtype.val : π.ker → P) ⁻¹' K) := hemb.isCompact_preimage hKc
  refine lt_of_le_of_lt
    (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hDf ν)
      (D' := (Subtype.val : π.ker → P) ⁻¹' K) (.of_forall fun m => ?_)) hKc'.measure_lt_top
  obtain ⟨γ, hγ, hπγ, hmem⟩ := hK m m.2
  have hγk : γ ∈ π.ker := hπγ
  refine ⟨⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 hγ⟩, ?_⟩
  exact hmem

end GlobalTheory.CompanionTheory.SplitExtLat
