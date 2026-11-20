import Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafGlueTwoPf GlobalTheory.GlueModels

namespace LateralTheory.E.LeafGlueTwoPfFP

def LeafPushoutQS : Prop := ∀ {DW DU DV : Scheme.{0}} (φU : DW ⟶ DU) (φV : DW ⟶ DV) [IsOpenImmersion φU]
    [IsOpenImmersion φV], CompactSpace DW → QuasiSeparatedSpace DW → QuasiSeparatedSpace DU →
    QuasiSeparatedSpace DV → QuasiSeparatedSpace (pushout φU φV : Scheme.{0})

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Introduce a local definition for the expression. Apply the first step, then apply the next step to every resulting obligation. Introduce a local definition for the expression. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components.

Supply the required witnesses or components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Supply the required witnesses or components. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem LateralTheory.E.LeafGlueTwoPfFP.LeafGlueTwo_of' (hQ : LateralTheory.E.LeafGlueTwoPfFP.LeafPushoutQS) :
    LateralTheory.E.LeafObjGluePf.LeafGlueTwo :=
  LateralTheory.E.LeafGlueTwoPf.LeafGlueTwo_of (LateralTheory.E.LeafGlueTwoPfFP.pushout_finitePresentation_of_quasiSeparated hQ)

end
