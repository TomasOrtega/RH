import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphismsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibProperClosed

/- English proof (translation)
Introduce `O _ _ _ hI Y P q s C hs hq hk hC hy`. Use `set U : Set P := coborder (Set.range q) with hUdef`. Establish `hUo : IsOpen U` using `q.isLocallyClosed_range.isOpen_coborder`. Establish `hqU : Set.range q = U ∩ closure (Set.range q)` using `(coborder_inter_closure).symm`. Establish `hZsub : closure (q '' C) ⊆ closure (Set.range q)` using `closure_mono (Set.image_subset_range _ _)`.

Establish `himg : q '' closure C = closure (q '' C) ∩ U`. Rewrite using `[q.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range, hqU]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, -⟩`.

Conclude with `⟨h1, h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, h2, hZsub h1⟩`. Establish `hZc : IsClosed (closure (q '' C))` using `isClosed_closure`. Establish `hZirr : IsIrreducible (closure (q '' C))` using `(hC.image q q.continuous.continuousOn).closure`.

Establish `hZk : _root_.IsPreconnected (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O})`. Set `I` to `Scheme.IdealSheafData.vanishingIdeal (⟨closure (q '' C), hZc⟩ : TopologicalSpace.Closeds P)`. Establish `hrange : Set.range I.subschemeι = closure (q '' C)`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Both sides reduce to the same expression.

Use `haveI : IsProper (I.subschemeι ≫ s) := inferInstance`. Establish `hne : Nonempty I.subscheme`. Take `⟨c, hc⟩` from `hC.nonempty`. Establish `: q c ∈ Set.range I.subschemeι` using `by rw [hrange]; exact subset_closure ⟨c, hc, rfl⟩`. Take `⟨w, -⟩` from `this`.

Conclude with `⟨w⟩`. Establish `hpc : _root_.IsPreconnected (Set.univ : Set I.subscheme)`. Rewrite using `[← I.subschemeι.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hrange]`. Conclude with `hZirr.2.isPreconnected`. Use `haveI : ConnectedSpace I.subscheme := { toPreconnectedSpace := ⟨hpc⟩, toNonempty := hne }`.

Use `haveI hsp := GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms GlobalTheory.T.formalAlgebraisation_morphisms' O _ (I.subschemeι ≫ s) inferInstance inferInstance`. Establish `hT : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s)) = (I.subschemeι ≫ s) ⁻¹' {IsLocalRing.closedPoint O}`. Establish `h` using `Scheme.Pullback.range_fst (I.subschemeι ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))`. Rewrite `h` using `[GlobalTheory.SpecialConn.range_residue]`. Conclude with `h`.

Establish `hR : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s) ≫ I.subschemeι) = closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hT, ← hrange, Set.inter_comm, ← Set.image_preimage_eq_inter_range]`. Both sides reduce to the same expression. Rewrite using `[← hR]`. Conclude with `isPreconnected_range (Scheme.Hom.continuous _)`.

Establish `hkU : IsClosed ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U)`. Set `res` to `Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))`. Use `haveI : IsClosedImmersion res := IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective`. Use `haveI : IsProper (pullback.snd (q ≫ s) res ≫ res) := inferInstance`. Use `haveI : IsProper ((pullback.fst (q ≫ s) res ≫ q) ≫ s) := by`.

Rewrite using `[Category.assoc, pullback.condition]`. Use `infer_instance`. Use `haveI : IsProper (pullback.fst (q ≫ s) res ≫ q) := IsProper.of_comp _ s`. Establish `hF : Set.range (pullback.fst (q ≫ s) res) = (q ≫ s) ⁻¹' {IsLocalRing.closedPoint O}`. Establish `h` using `Scheme.Pullback.range_fst (q ≫ s) res`.

Rewrite `h` using `[GlobalTheory.SpecialConn.range_residue]`. Conclude with `h`. Establish `hcl` using `(pullback.fst (q ≫ s) res ≫ q).isClosedMap _ ((isClosed_closure (s := C)).preimage (pullback.fst (q ≫ s) res).continuous)`. Establish `e : (pullback.fst (q ≫ s) res ≫ q) '' (pullback.fst (q ≫ s) res ⁻¹' closure C) = (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range, hF]`.

Express the relevant statement in the definitionally equal form `q '' (closure C ∩ q ⁻¹' (s ⁻¹' {IsLocalRing.closedPoint O})) = _`. Rewrite using `[Set.image_inter_preimage, himg]`. Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff]`. The claim follows by propositional logic.

Rewrite using `[← e]`. Conclude with `hcl`. Establish `hne : ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U).Nonempty`. Take `⟨y, hyC, hy⟩` from `hy`. Establish `h1 : q y ∈ closure (q '' C) ∩ U` using `himg ▸ ⟨y, hyC, rfl⟩`.

Conclude with `⟨q y, ⟨h1.1, hy⟩, h1.2⟩`. Establish `hZkU : closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O} ⊆ U`. Introduce `z hz`. Assume the negation of the conclusion as `hzU`. Take `⟨w, hw, hw1, hw2⟩` from `hZk U _ hUo hkU.isOpen_compl (fun x _ => by`.

Distinguish the cases in `h : x ∈ U`. Conclude with `Or.inl h`. Conclude with `Or.inr fun h' => h h'.2)`. Use the proof step `(by obtain ⟨x, hx1, hx2⟩ := hne; exact ⟨x, hx1, hx2⟩) ⟨z, hz, fun h => hzU h.2⟩`. Conclude with `hw2 ⟨hw, hw1⟩`.

Establish `hZU : closure (q '' C) ⊆ U`. Introduce `z hz`. Assume the negation of the conclusion as `hzU`. Establish `hcl : IsClosed (s '' (closure (q '' C) \ U))` using `s.isClosedMap _ (hZc.sdiff hUo)`. Establish `hsp : s z ⤳ IsLocalRing.closedPoint O` using `(PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (s z).2.ne_top)`.

Take `⟨z', ⟨hz'Z, hz'U⟩, hz'⟩` from `hsp.mem_closed hcl ⟨z, ⟨hz, hzU⟩, rfl⟩`. Conclude with `hz'U (hZkU ⟨hz'Z, hz'⟩)`. Rewrite using `[himg, Set.inter_eq_left.2 hZU]`. Conclude with `hZc`.
-/
theorem isClosed_image_closure : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y P : Scheme.{0}) (q : Y ⟶ P)
    (s : P ⟶ Spec (CommRingCat.of O)) (C : Set Y), IsProper s → IsImmersion q →
    IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) →
    IsIrreducible C → (∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O) →
    IsClosed (q '' closure C) := by
  intro O _ _ _ hI Y P q s C hs hq hk hC hy
  set U : Set P := coborder (Set.range q) with hUdef
  have hUo : IsOpen U := q.isLocallyClosed_range.isOpen_coborder
  have hqU : Set.range q = U ∩ closure (Set.range q) := (coborder_inter_closure).symm
  have hZsub : closure (q '' C) ⊆ closure (Set.range q) := closure_mono (Set.image_subset_range _ _)
  have himg : q '' closure C = closure (q '' C) ∩ U := by
    rw [q.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range, hqU]
    ext x
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hZsub h1⟩
  have hZc : IsClosed (closure (q '' C)) := isClosed_closure
  have hZirr : IsIrreducible (closure (q '' C)) := (hC.image q q.continuous.continuousOn).closure

  have hZk : _root_.IsPreconnected (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) := by
    let I := Scheme.IdealSheafData.vanishingIdeal (⟨closure (q '' C), hZc⟩ : TopologicalSpace.Closeds P)
    have hrange : Set.range I.subschemeι = closure (q '' C) := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
    haveI : IsProper (I.subschemeι ≫ s) := inferInstance
    have hne : Nonempty I.subscheme := by
      obtain ⟨c, hc⟩ := hC.nonempty
      have : q c ∈ Set.range I.subschemeι := by rw [hrange]; exact subset_closure ⟨c, hc, rfl⟩
      obtain ⟨w, -⟩ := this
      exact ⟨w⟩
    have hpc : _root_.IsPreconnected (Set.univ : Set I.subscheme) := by
      rw [← I.subschemeι.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hrange]
      exact hZirr.2.isPreconnected
    haveI : ConnectedSpace I.subscheme := { toPreconnectedSpace := ⟨hpc⟩, toNonempty := hne }
    haveI hsp := GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms GlobalTheory.T.formalAlgebraisation_morphisms' O _
      (I.subschemeι ≫ s) inferInstance inferInstance
    have hT : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s)) =
        (I.subschemeι ≫ s) ⁻¹' {IsLocalRing.closedPoint O} := by
      have h := Scheme.Pullback.range_fst (I.subschemeι ≫ s)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
      rw [GlobalTheory.SpecialConn.range_residue] at h
      exact h
    have hR : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s) ≫ I.subschemeι) =
        closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O} := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hT, ← hrange, Set.inter_comm,
        ← Set.image_preimage_eq_inter_range]
      rfl
    rw [← hR]
    exact isPreconnected_range (Scheme.Hom.continuous _)

  have hkU : IsClosed ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U) := by
    let res := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
    haveI : IsClosedImmersion res :=
      IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
    haveI : IsProper (pullback.snd (q ≫ s) res ≫ res) := inferInstance
    haveI : IsProper ((pullback.fst (q ≫ s) res ≫ q) ≫ s) := by
      rw [Category.assoc, pullback.condition]; infer_instance
    haveI : IsProper (pullback.fst (q ≫ s) res ≫ q) := IsProper.of_comp _ s
    have hF : Set.range (pullback.fst (q ≫ s) res) = (q ≫ s) ⁻¹' {IsLocalRing.closedPoint O} := by
      have h := Scheme.Pullback.range_fst (q ≫ s) res
      rw [GlobalTheory.SpecialConn.range_residue] at h
      exact h
    have hcl := (pullback.fst (q ≫ s) res ≫ q).isClosedMap _
      ((isClosed_closure (s := C)).preimage (pullback.fst (q ≫ s) res).continuous)
    have e : (pullback.fst (q ≫ s) res ≫ q) '' (pullback.fst (q ≫ s) res ⁻¹' closure C) =
        (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range, hF]
      change q '' (closure C ∩ q ⁻¹' (s ⁻¹' {IsLocalRing.closedPoint O})) = _
      rw [Set.image_inter_preimage, himg]
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rw [← e]; exact hcl
  have hne : ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U).Nonempty := by
    obtain ⟨y, hyC, hy⟩ := hy
    have h1 : q y ∈ closure (q '' C) ∩ U := himg ▸ ⟨y, hyC, rfl⟩
    exact ⟨q y, ⟨h1.1, hy⟩, h1.2⟩
  have hZkU : closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O} ⊆ U := by
    intro z hz
    by_contra hzU
    obtain ⟨w, hw, hw1, hw2⟩ := hZk U _ hUo hkU.isOpen_compl
        (fun x _ => by
          by_cases h : x ∈ U
          · exact Or.inl h
          · exact Or.inr fun h' => h h'.2)
        (by obtain ⟨x, hx1, hx2⟩ := hne; exact ⟨x, hx1, hx2⟩) ⟨z, hz, fun h => hzU h.2⟩
    exact hw2 ⟨hw, hw1⟩
  have hZU : closure (q '' C) ⊆ U := by
    intro z hz
    by_contra hzU
    have hcl : IsClosed (s '' (closure (q '' C) \ U)) := s.isClosedMap _ (hZc.sdiff hUo)
    have hsp : s z ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (s z).2.ne_top)
    obtain ⟨z', ⟨hz'Z, hz'U⟩, hz'⟩ := hsp.mem_closed hcl ⟨z, ⟨hz, hzU⟩, rfl⟩
    exact hz'U (hZkU ⟨hz'Z, hz'⟩)
  rw [himg, Set.inter_eq_left.2 hZU]
  exact hZc

end GlobalTheory.FibProperClosed
