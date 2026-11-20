import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order TopologicalSpace Topology

namespace LateralTheory.E.LeafGlueDimPf

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem dim_eq_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X = max (topologicalKrullDim U) (topologicalKrullDim V) :=
  le_antisymm (dim_le_of_cover f g hf hg hc)
    (max_le hf.isInducing.topologicalKrullDim_le hg.isInducing.topologicalKrullDim_le)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dim_Sp {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) :
    topologicalKrullDim (Sp A) = ringKrullDim A :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities.
-/
theorem LeafGlueDim_of : LateralTheory.E.LeafGlueProperPf.LeafGlueDim := by
  intro Ω L _ _ _ A B u h G
  have hA : topologicalKrullDim (Sp A) = 1 := (dim_Sp A).trans h.2.2.2.2.2.2.2.1
  have hB : topologicalKrullDim (Sp B) = 1 := (dim_Sp B).trans h.2.2.2.2.2.2.2.2.1
  have := G.hiA; have := G.hiB
  rw [dim_eq_of_cover G.iA.base G.iB.base G.iA.isOpenEmbedding G.iB.isOpenEmbedding G.cover, hA, hB, max_self]

end LateralTheory.E.LeafGlueDimPf
