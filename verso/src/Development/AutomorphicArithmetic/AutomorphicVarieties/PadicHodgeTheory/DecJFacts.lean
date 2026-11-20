import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocD
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ _ l _ j`. Use `haveI : IsAlgClosure ℚ Ω := Examples₂.LB.isAlgClosureQ F Ω`. Establish `hj : ∀ x : Ω, x ∈ placeJ j ↔ ‖j x‖ ≤ 1`. Introduce `x`. Express the relevant statement in the definitionally equal form `(Valued.v : Valuation (Om l) NNReal) (j x) ≤ 1 ↔ _`.

Rewrite using `[← NNReal.coe_le_coe]`. Conclude with `Iff.rfl`. Set `e` to `Examples₂.LB.eDec (E := F) hj`. Establish `he : Continuous e` using `Examples₂.LB.continuous_eDec hj`. Establish `hes : Continuous e.symm` using `Examples₂.LB.continuous_eDec_symm hj`.

Establish `hc : ∀ g x, ((e g : _) : GQ l) (j x) = j ((g : G F Ω) x)` using `Examples₂.LB.eDec_comm hj`. Establish `hK : ∀ x : ↥(UpperTheory.V.Af.decJ F j), x.1.2 ∈ (Examples₂.LB.KwF (E` using `F) j).fixingSubgroup := by`. Introduce `x`. Use `Examples₂.LB.mem_GK_of_fix j _ fun y => ?_` and prove the remaining obligations. Use `x.2 (algebraMap F Ω y)` as an intermediate fact.

Rewrite `this` using `[AlgEquiv.commutes]`. Conclude with `this`. Establish `hfst : ∀ x : ↥(UpperTheory.V.Af.decJ F j), ((e.symm ⟨x.1.2, hK x⟩ : _) : G F Ω) = x.1.1`. Introduce `x`. Use `AlgEquiv.ext fun y => j.injective ?_` and prove the remaining obligations.

Rewrite using `[← hc, MulEquiv.apply_symm_apply]`. Conclude with `x.2 y`. Set `h : ↥(UpperTheory.V.Af.decJ F j) ≃ₜ ↥(Examples₂.LB.KwF (E` to `F) j).fixingSubgroup := { toFun := fun x => ⟨x.1.2, hK x⟩ invFun := fun σ => ⟨(((e.symm σ : _) : G F Ω), σ.1), fun y => by`. Use `hc (e.symm σ) y` as an intermediate fact. Rewrite `this` using `[MulEquiv.apply_symm_apply]`.

Conclude with `this⟩`. Use `left_inv := fun x => Subtype.ext (Prod.ext (hfst x) rfl)`. Use `right_inv := fun σ => rfl`. Use `continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _`. Use `continuous_invFun := ((continuous_subtype_val.comp hes).prodMk continuous_subtype_val).subtype_mk _ }`.

Set `e' : ↥(Examples₂.LB.KwF (E` to `F) j).fixingSubgroup ≃ₜ ↥(Dec (F := F) (placeJ j)) := { toEquiv := e.symm.toEquiv, continuous_toFun := hes, continuous_invFun := he }`. Establish `h1 : ⇑((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype) = Subtype.val ∘ (h.trans e')`. Use function extensionality and compare the values at `fun x => (hfst x).symm`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(IntermediateField.fixingSubgroup_isOpen (Examples₂.LB.KwF (E := F) j)).isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding`.

Rewrite using `[h1]`. Conclude with `IsEmbedding.subtypeVal.comp (h.trans e').isEmbedding`. Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[MonoidHom.coe_range, h1, Set.range_comp, (h.trans e').surjective.range_eq, Set.image_univ, Subtype.range_coe_subtype]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Loc.decJFacts :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l), IsOpenEmbedding ((MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype) ∧ IsEmbedding ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype) ∧ ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype).range = Dec (F := F) (placeJ j) := by
  intro F Ω _ _ _ _ _ _ l _ j
  haveI : IsAlgClosure ℚ Ω := Examples₂.LB.isAlgClosureQ F Ω
  have hj : ∀ x : Ω, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
    intro x
    change (Valued.v : Valuation (Om l) NNReal) (j x) ≤ 1 ↔ _
    rw [← NNReal.coe_le_coe]
    exact Iff.rfl
  let e := Examples₂.LB.eDec (E := F) hj
  have he : Continuous e := Examples₂.LB.continuous_eDec hj
  have hes : Continuous e.symm := Examples₂.LB.continuous_eDec_symm hj
  have hc : ∀ g x, ((e g : _) : GQ l) (j x) = j ((g : G F Ω) x) := Examples₂.LB.eDec_comm hj
  have hK : ∀ x : ↥(UpperTheory.V.Af.decJ F j), x.1.2 ∈ (Examples₂.LB.KwF (E := F) j).fixingSubgroup := by
    intro x
    refine Examples₂.LB.mem_GK_of_fix j _ fun y => ?_
    have := x.2 (algebraMap F Ω y)
    rw [AlgEquiv.commutes] at this
    exact this
  have hfst : ∀ x : ↥(UpperTheory.V.Af.decJ F j), ((e.symm ⟨x.1.2, hK x⟩ : _) : G F Ω) = x.1.1 := by
    intro x
    refine AlgEquiv.ext fun y => j.injective ?_
    rw [← hc, MulEquiv.apply_symm_apply]
    exact x.2 y
  let h : ↥(UpperTheory.V.Af.decJ F j) ≃ₜ ↥(Examples₂.LB.KwF (E := F) j).fixingSubgroup :=
    { toFun := fun x => ⟨x.1.2, hK x⟩
      invFun := fun σ => ⟨(((e.symm σ : _) : G F Ω), σ.1), fun y => by
        have := hc (e.symm σ) y
        rw [MulEquiv.apply_symm_apply] at this
        exact this⟩
      left_inv := fun x => Subtype.ext (Prod.ext (hfst x) rfl)
      right_inv := fun σ => rfl
      continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((continuous_subtype_val.comp hes).prodMk continuous_subtype_val).subtype_mk _ }
  let e' : ↥(Examples₂.LB.KwF (E := F) j).fixingSubgroup ≃ₜ ↥(Dec (F := F) (placeJ j)) :=
    { toEquiv := e.symm.toEquiv, continuous_toFun := hes, continuous_invFun := he }
  have h1 : ⇑((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype) = Subtype.val ∘ (h.trans e') :=
    funext fun x => (hfst x).symm
  refine ⟨?_, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen (Examples₂.LB.KwF (E := F) j)).isOpenEmbedding_subtypeVal.comp
      h.isOpenEmbedding
  · rw [h1]
    exact IsEmbedding.subtypeVal.comp (h.trans e').isEmbedding
  · apply SetLike.coe_injective
    rw [MonoidHom.coe_range, h1, Set.range_comp, (h.trans e').surjective.range_eq, Set.image_univ, Subtype.range_coe_subtype]
    rfl
