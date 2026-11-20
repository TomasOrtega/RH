import Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafGlueTwoPf GlobalTheory.GlueModels

namespace LateralTheory.E.LeafGlueTwoPfFP

def LeafPushoutQS : Prop := ∀ {DW DU DV : Scheme.{0}} (φU : DW ⟶ DU) (φV : DW ⟶ DV) [IsOpenImmersion φU]
    [IsOpenImmersion φV], CompactSpace DW → QuasiSeparatedSpace DW → QuasiSeparatedSpace DU →
    QuasiSeparatedSpace DV → QuasiSeparatedSpace (pushout φU φV : Scheme.{0})

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Introduce `DW DU DV S φU φV _ _ qU qV h hS ⟨l1, c1, s1⟩ ⟨l2, c2, s2⟩ ⟨l3, c3, s3⟩`. Establish `: CompactSpace DU` using `QuasiCompact.compactSpace_of_compactSpace qU`. Establish `: CompactSpace DV` using `QuasiCompact.compactSpace_of_compactSpace qV`. Establish `: CompactSpace DW` using `QuasiCompact.compactSpace_of_compactSpace (φU ≫ qU)`. Establish `: QuasiSeparatedSpace DU` using `quasiSeparatedSpace_of_quasiSeparated qU`.

Establish `: QuasiSeparatedSpace DV` using `quasiSeparatedSpace_of_quasiSeparated qV`. Establish `: QuasiSeparatedSpace DW` using `quasiSeparatedSpace_of_quasiSeparated (φU ≫ qU)`. Use `isOpenImmersion_inl φU φV` as an intermediate fact. Use `isOpenImmersion_inr φU φV` as an intermediate fact. Set `T : Bool → Scheme.{0}` to `fun i => Bool.rec DU DV i`.

Set `t : ∀ i, T i ⟶ pushout φU φV` to `fun i => Bool.rec (motive := fun i => T i ⟶ pushout φU φV) (pushout.inl φU φV) (pushout.inr φU φV) i`. Apply the tactic sequence `have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption`. Set `𝒰 : (pushout φU φV).OpenCover` to `Scheme.Cover.mkOfCovers Bool T t (fun x => by`. Break down `pushout_cover φU φV x with ⟨y, hy⟩ | ⟨y, hy⟩` into its components or cases. Conclude with `⟨false, y, hy⟩`.

Conclude with `⟨true, y, hy⟩)`. Establish `hL : LocallyOfFinitePresentation (pushout.desc qU qV h)`. Use `IsZariskiLocalAtSource.of_openCover 𝒰 ?_` and prove the remaining obligations. Introduce and unpack `(_ | _)`. Express the relevant statement in the definitionally equal form `LocallyOfFinitePresentation (pushout.inl φU φV ≫ pushout.desc qU qV h)`.

Rewrite using `[pushout.inl_desc]`. Conclude with `l1`. Express the relevant statement in the definitionally equal form `LocallyOfFinitePresentation (pushout.inr φU φV ≫ pushout.desc qU qV h)`. Rewrite using `[pushout.inr_desc]`. Conclude with `l2`.

Establish `hC : CompactSpace (pushout φU φV : Scheme.{0})`. Use `⟨?_⟩` and prove the remaining obligations. Establish `hu : (Set.univ : Set (pushout φU φV : Scheme.{0})) = Set.range (pushout.inl φU φV) ∪ Set.range (pushout.inr φU φV)`. Use extensionality with `x`. Simplify using `using pushout_cover φU φV x`.

Rewrite using `[hu]`. Conclude with `(isCompact_range (pushout.inl φU φV).continuous).union (isCompact_range (pushout.inr φU φV).continuous)`. Establish `hQS` using `hQ φU φV inferInstance inferInstance inferInstance inferInstance`. Conclude with `⟨hL, inferInstance, inferInstance⟩`.
-/
theorem pushout_finitePresentation_of_quasiSeparated (hQ : LeafPushoutQS) : LeafPushoutFP := by
  intro DW DU DV S φU φV _ _ qU qV h hS ⟨l1, c1, s1⟩ ⟨l2, c2, s2⟩ ⟨l3, c3, s3⟩
  have : CompactSpace DU := QuasiCompact.compactSpace_of_compactSpace qU
  have : CompactSpace DV := QuasiCompact.compactSpace_of_compactSpace qV
  have : CompactSpace DW := QuasiCompact.compactSpace_of_compactSpace (φU ≫ qU)
  have : QuasiSeparatedSpace DU := quasiSeparatedSpace_of_quasiSeparated qU
  have : QuasiSeparatedSpace DV := quasiSeparatedSpace_of_quasiSeparated qV
  have : QuasiSeparatedSpace DW := quasiSeparatedSpace_of_quasiSeparated (φU ≫ qU)
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV
  let T : Bool → Scheme.{0} := fun i => Bool.rec DU DV i
  let t : ∀ i, T i ⟶ pushout φU φV := fun i => Bool.rec (motive := fun i => T i ⟶ pushout φU φV)
    (pushout.inl φU φV) (pushout.inr φU φV) i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : (pushout φU φV).OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases pushout_cover φU φV x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  have hL : LocallyOfFinitePresentation (pushout.desc qU qV h) := by
    refine IsZariskiLocalAtSource.of_openCover 𝒰 ?_
    rintro (_ | _)
    · change LocallyOfFinitePresentation (pushout.inl φU φV ≫ pushout.desc qU qV h)
      rw [pushout.inl_desc]; exact l1
    · change LocallyOfFinitePresentation (pushout.inr φU φV ≫ pushout.desc qU qV h)
      rw [pushout.inr_desc]; exact l2
  have hC : CompactSpace (pushout φU φV : Scheme.{0}) := by
    refine ⟨?_⟩
    have hu : (Set.univ : Set (pushout φU φV : Scheme.{0})) =
        Set.range (pushout.inl φU φV) ∪ Set.range (pushout.inr φU φV) := by
      ext x; simpa using pushout_cover φU φV x
    rw [hu]
    exact (isCompact_range (pushout.inl φU φV).continuous).union (isCompact_range (pushout.inr φU φV).continuous)
  have hQS := hQ φU φV inferInstance inferInstance inferInstance inferInstance
  exact ⟨hL, inferInstance, inferInstance⟩

end LateralTheory.E.LeafGlueTwoPfFP

/- English proof (translation)
The claim follows from `LateralTheory.E.LeafGlueTwoPf.LeafGlueTwo_of (LateralTheory.E.LeafGlueTwoPfFP.pushout_finitePresentation_of_quasiSeparated hQ)`.
-/
theorem LateralTheory.E.LeafGlueTwoPfFP.LeafGlueTwo_of' (hQ : LateralTheory.E.LeafGlueTwoPfFP.LeafPushoutQS) :
    LateralTheory.E.LeafObjGluePf.LeafGlueTwo :=
  LateralTheory.E.LeafGlueTwoPf.LeafGlueTwo_of (LateralTheory.E.LeafGlueTwoPfFP.pushout_finitePresentation_of_quasiSeparated hQ)

end
