import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Use `⟨fun {Z X} ι hι => ⟨⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `Z' X' Z X ι' ι f u h U hU`. Express the relevant statement in the definitionally equal form `f ⁻¹' (U : Set X) = _`. Rewrite using `[hU, Set.preimage_compl, ← Scheme.Pullback.range_fst]`. Use `congr 1`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨h.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨h.isoPullback.hom y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.offEx_holds :
    UpperTheory.Gal.KunnethLefschetz.OffEx := by
  refine ⟨fun {Z X} ι hι => ⟨⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩, rfl⟩, ?_⟩
  intro Z' X' Z X ι' ι f u h U hU
  change f ⁻¹' (U : Set X) = _
  rw [hU, Set.preimage_compl, ← Scheme.Pullback.range_fst]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.hom y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
