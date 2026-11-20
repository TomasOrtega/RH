import Mathlib

noncomputable section

namespace PI.VolStabSW.TopoPolish

open Topology TopologicalSpace Set

/- English proof (translation)
Use `letI := TopologicalSpace.metrizableSpaceMetric Y`. Establish `hemb : IsEmbedding ((↑) : Y → UniformSpace.Completion Y)` using `(UniformSpace.Completion.isUniformEmbedding_coe Y).isEmbedding`. Establish `hdense : DenseRange ((↑) : Y → UniformSpace.Completion Y)` using `UniformSpace.Completion.denseRange_coe`. Establish `hopen : IsOpen (range ((↑) : Y → UniformSpace.Completion Y))`. Rewrite using `[isOpen_iff_forall_mem_open]`.

Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨K, hK, hKy⟩` from `exists_compact_mem_nhds y`. Take `⟨V, hVK, hVo, hyV⟩` from `mem_nhds_iff.1 hKy`. Take `⟨U, hUo, hUV⟩` from `hemb.isInducing.isOpen_iff.1 hVo`. Use `⟨U, ?_, hUo, ?_⟩` and prove the remaining obligations.

Establish `hcl : IsClosed (((↑) : Y → UniformSpace.Completion Y) '' K)` using `(hK.image hemb.continuous).isClosed`. Combine the equalities or inequalities in the displayed calculation. Apply `closure_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨hz, ⟨z, rfl⟩⟩`. Use `⟨z, hVK ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[← hUV]`. Conclude with `hz`. Use `_ = ((↑) : Y → UniformSpace.Completion Y) '' K := hcl.closure_eq`. Use `_ ⊆ range ((↑) : Y → UniformSpace.Completion Y) := image_subset_range _ _`. Use `show y ∈ ((↑) : Y → UniformSpace.Completion Y) ⁻¹' U`.

Rewrite using `[hUV]`. Conclude with `hyV`. Establish `: PolishSpace (range ((↑) : Y → UniformSpace.Completion Y))` using `hopen.polishSpace`. Conclude with `hemb.toHomeomorph.isClosedEmbedding.polishSpace`.
-/
theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  letI := TopologicalSpace.metrizableSpaceMetric Y
  have hemb : IsEmbedding ((↑) : Y → UniformSpace.Completion Y) :=
    (UniformSpace.Completion.isUniformEmbedding_coe Y).isEmbedding
  have hdense : DenseRange ((↑) : Y → UniformSpace.Completion Y) :=
    UniformSpace.Completion.denseRange_coe
  have hopen : IsOpen (range ((↑) : Y → UniformSpace.Completion Y)) := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨y, rfl⟩
    obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
    obtain ⟨V, hVK, hVo, hyV⟩ := mem_nhds_iff.1 hKy
    obtain ⟨U, hUo, hUV⟩ := hemb.isInducing.isOpen_iff.1 hVo
    refine ⟨U, ?_, hUo, ?_⟩
    · have hcl : IsClosed (((↑) : Y → UniformSpace.Completion Y) '' K) :=
        (hK.image hemb.continuous).isClosed
      calc U ⊆ closure (U ∩ range ((↑) : Y → UniformSpace.Completion Y)) :=
            hdense.open_subset_closure_inter hUo
        _ ⊆ closure (((↑) : Y → UniformSpace.Completion Y) '' K) := by
            apply closure_mono
            rintro _ ⟨hz, ⟨z, rfl⟩⟩
            refine ⟨z, hVK ?_, rfl⟩
            rw [← hUV]
            exact hz
        _ = ((↑) : Y → UniformSpace.Completion Y) '' K := hcl.closure_eq
        _ ⊆ range ((↑) : Y → UniformSpace.Completion Y) := image_subset_range _ _
    · show y ∈ ((↑) : Y → UniformSpace.Completion Y) ⁻¹' U
      rw [hUV]
      exact hyV
  have : PolishSpace (range ((↑) : Y → UniformSpace.Completion Y)) := hopen.polishSpace
  exact hemb.toHomeomorph.isClosedEmbedding.polishSpace

end PI.VolStabSW.TopoPolish
