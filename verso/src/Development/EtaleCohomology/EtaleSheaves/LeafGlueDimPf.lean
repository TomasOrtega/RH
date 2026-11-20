import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order TopologicalSpace Topology

namespace LateralTheory.E.LeafGlueDimPf

/- English proof (translation)
Unfold `topologicalKrullDim`. Rewrite using `[krullDim_eq_iSup_coheight]`. Use `iSup_le fun Z => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `Z.2.nonempty`. Establish `hzu : z ∈ Set.range f ∪ Set.range g` using `hc ▸ Set.mem_univ z`.

Break down `hzu with ⟨w, rfl⟩ | ⟨w, rfl⟩` into its components or cases. Set `T` to `(IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨Z, ⟨w, hz⟩⟩`. Establish `hT : IrreducibleCloseds.map f hf.continuous T = Z`. Use `(IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩` as an intermediate fact. Conclude with `congrArg Subtype.val this`.

Rewrite using `[← hT, hf.coheight_map]`. Conclude with `le_trans (coheight_le_krullDim T) le_sup_left`. Set `T` to `(IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).symm ⟨Z, ⟨w, hz⟩⟩`. Establish `hT : IrreducibleCloseds.map g hg.continuous T = Z`. Use `(IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩` as an intermediate fact.

Conclude with `congrArg Subtype.val this`. Rewrite using `[← hT, hg.coheight_map]`. Conclude with `le_trans (coheight_le_krullDim T) le_sup_right`.
-/
theorem dim_le_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X ≤ max (topologicalKrullDim U) (topologicalKrullDim V) := by
  unfold topologicalKrullDim
  rw [krullDim_eq_iSup_coheight]
  refine iSup_le fun Z => ?_
  obtain ⟨z, hz⟩ := Z.2.nonempty
  have hzu : z ∈ Set.range f ∪ Set.range g := hc ▸ Set.mem_univ z
  rcases hzu with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map f hf.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hf.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_left
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map g hg.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hg.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_right

/- English proof (translation)
The claim follows from `le_antisymm (dim_le_of_cover f g hf hg hc) (max_le hf.isInducing.topologicalKrullDim_le hg.isInducing.topologicalKrullDim_le)`.
-/
theorem dim_eq_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X = max (topologicalKrullDim U) (topologicalKrullDim V) :=
  le_antisymm (dim_le_of_cover f g hf hg hc)
    (max_le hf.isInducing.topologicalKrullDim_le hg.isInducing.topologicalKrullDim_le)

/- English proof (translation)
The claim follows from `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A`.
-/
theorem dim_Sp {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) :
    topologicalKrullDim (Sp A) = ringKrullDim A :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

/- English proof (translation)
Introduce `Ω L _ _ _ A B u h G`. Establish `hA : topologicalKrullDim (Sp A) = 1` using `(dim_Sp A).trans h.2.2.2.2.2.2.2.1`. Establish `hB : topologicalKrullDim (Sp B) = 1` using `(dim_Sp B).trans h.2.2.2.2.2.2.2.2.1`. Use `G.hiA` as an intermediate fact. Use `G.hiB` as an intermediate fact.

Rewrite using `[dim_eq_of_cover G.iA.base G.iB.base G.iA.isOpenEmbedding G.iB.isOpenEmbedding G.cover, hA, hB, max_self]`.
-/
theorem LeafGlueDim_of : LateralTheory.E.LeafGlueProperPf.LeafGlueDim := by
  intro Ω L _ _ _ A B u h G
  have hA : topologicalKrullDim (Sp A) = 1 := (dim_Sp A).trans h.2.2.2.2.2.2.2.1
  have hB : topologicalKrullDim (Sp B) = 1 := (dim_Sp B).trans h.2.2.2.2.2.2.2.2.1
  have := G.hiA; have := G.hiB
  rw [dim_eq_of_cover G.iA.base G.iB.base G.iA.isOpenEmbedding G.iB.isOpenEmbedding G.cover, hA, hB, max_self]

end LateralTheory.E.LeafGlueDimPf
