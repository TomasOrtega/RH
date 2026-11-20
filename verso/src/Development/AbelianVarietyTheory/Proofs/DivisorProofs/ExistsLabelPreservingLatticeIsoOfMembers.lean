import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRLocalEmbeddingNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePointsJoinedBySpecialisationChainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMemberThroughModelPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftToSemiAbelianModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtendingModelAboveThetaSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMembersLatticesIsoOfSpecializesDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberBaseChangeInjectiveLocalHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.GMem

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

/- English proof (translation)
Take `⟨K₁, hK₁, hl₁⟩` from `h₁`. Take `⟨K₂, hK₂, hl₂⟩` from `h₂`. Use `⟨K₁.trans K₂, fun a mu => ?_, fun a mu h => hl₂ a _ (hl₁ a mu h)⟩` and prove the remaining obligations. Simplify using `only [AddEquiv.trans_apply, hK₁, hK₂]`.
-/
theorem LatTo.trans
    {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {t₀ : X₀ → V₀} {δ₀ : I → X₀ → X₀}
    {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁}
    {Y₁ : Type} [AddCommGroup Y₁] {t₁ : Y₁ → V₁} {δ₁ : I → Y₁ → Y₁}
    {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂}
    {Y₂ : Type} [AddCommGroup Y₂] {t₂ : Y₂ → V₂} {δ₂ : I → Y₂ → Y₂}
    {𝔪₀ : GMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀} {𝔪₁ : GMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁} {𝔪₂ : GMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂}
    (h₁ : 𝔪₀.LatTo 𝔪₁) (h₂ : 𝔪₁.LatTo 𝔪₂) : 𝔪₀.LatTo 𝔪₂ := by
  obtain ⟨K₁, hK₁, hl₁⟩ := h₁
  obtain ⟨K₂, hK₂, hl₂⟩ := h₂
  refine ⟨K₁.trans K₂, fun a mu => ?_, fun a mu h => hl₂ a _ (hl₁ a mu h)⟩
  simp only [AddEquiv.trans_apply, hK₁, hK₂]

/- English proof (translation)
Take `⟨K, hK, hl⟩` from `h`. Establish `y₀` using `GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀ 𝔪₀`. Establish `y₁` using `GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪`. Use `⟨K.symm, fun a mu => K.injective ?_, fun a mu' h => ?_⟩` and prove the remaining obligations. Rewrite using `[K.apply_symm_apply, hK, K.apply_symm_apply]`.

Take `⟨mu, hmu⟩` from `y₀.1 a`. Take `⟨w, hw⟩` from `(y₁.2.2.1 a (K mu) mu' (hl a mu hmu)).1 h`. Use `(y₀.2.2.1 a mu (K.symm mu') hmu).2 ⟨K.symm w, ?_⟩` and prove the remaining obligations. Rewrite using `[hw, map_add, K.symm_apply_apply, map_nsmul]`.
-/
theorem LatTo.symm
    {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {t₀ : X₀ → V₀} {δ₀ : I → X₀ → X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    {𝔪₀ : GMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀} {𝔪 : GMem X₁ z₁ act V ev X t δ} (h : 𝔪₀.LatTo 𝔪) : 𝔪.LatTo 𝔪₀ := by
  obtain ⟨K, hK, hl⟩ := h
  have y₀ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀ 𝔪₀
  have y₁ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪
  refine ⟨K.symm, fun a mu => K.injective ?_, fun a mu' h => ?_⟩
  · rw [K.apply_symm_apply, hK, K.apply_symm_apply]
  · obtain ⟨mu, hmu⟩ := y₀.1 a
    obtain ⟨w, hw⟩ := (y₁.2.2.1 a (K mu) mu' (hl a mu hmu)).1 h
    refine (y₀.2.2.1 a mu (K.symm mu') hmu).2 ⟨K.symm w, ?_⟩
    rw [hw, map_add, K.symm_apply_apply, map_nsmul]

end GlobalTheory.GSep.GMem

namespace GlobalTheory.GSep.Cmp

open GlobalTheory.GSep GlobalTheory.GSep.GMem

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(ξ ≫ πY) (closedPoint V) = z₁`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `X₁.M.Z.fromSpecStalk z₁ (spMap ev (closedPoint V)) = z₁`. Rewrite using `[show spMap ev (closedPoint V) = closedPoint _ from IsLocalRing.comap_closedPoint ev]`. Conclude with `Scheme.fromSpecStalk_closedPoint`.
-/
theorem closed_over {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    [IsLocalHom ev] {Y : Scheme.{0}} {πY : Y ⟶ X₁.M.Z} {ξ : Sp V ⟶ Y}
    (h : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) : πY (ξ (closedPoint V)) = z₁ := by
  change (ξ ≫ πY) (closedPoint V) = z₁
  rw [h]
  change X₁.M.Z.fromSpecStalk z₁ (spMap ev (closedPoint V)) = z₁
  rw [show spMap ev (closedPoint V) = closedPoint _ from IsLocalRing.comap_closedPoint ev]
  exact Scheme.fromSpecStalk_closedPoint

/- English proof (translation)
Take `⟨Y, πY, hY⟩` from `GlobalTheory.T.exists_semiAbelianExtendingModel_above_thetaSystem X₁`. Establish `lift : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValua …`. Introduce `V _ _ _ ev X _ t δ 𝔪`. Take `⟨V₁, _, _, _, _, j₁, hcn₁, hj₁, hl₁⟩` from `GlobalTheory.CompleteNormalDvr.exists_dvr_isCN V 𝔪.cn`. Use `haveI := 𝔪.loc`.

Use `haveI := hl₁`. Take `⟨V₂, _, _, _, _, j₂, ξ, hcn₂, hj₂, hl₂, hξ⟩` from `GlobalTheory.T.exists_trait_lift_to_semiAbelianModel X₁ z₁ Y πY hY V₁ (j₁.comp ev) inferInstance hcn₁`. Use `haveI := hl₂`. Establish `hj : Function.Injective (j₂.comp j₁)` using `hj₂.comp hj₁`. Take `⟨𝔫, -, hyy⟩` from `GlobalTheory.T.uniformisedMember_baseChange_injective_localHom I X₁ z₁ act V ev X t δ 𝔪 V₂ (j₂.comp j₁) (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₂) hj) hcn₂ hj inferInstance (fun v => IsLocalization.map_eq _ v)`.

Use `⟨V₂, inferInstance, inferInstance, inferInstance, inferInstance, (j₂.comp j₁).comp ev, _, 𝔫, ξ, ?_, AddEquiv.refl _, fun _ _ => rfl, hyy⟩` and prove the remaining obligations. Rewrite using `[hξ, RingHom.comp_assoc]`. Take `⟨W₀, _, _, _, _, e₀, s₀, 𝔫₀, ξ₀, hξ₀, a₀⟩` from `lift 𝔪₀`. Take `⟨W₁, _, _, _, _, e₁, s₁, 𝔫₁, ξ₁, hξ₁, a₁⟩` from `lift 𝔪`. Set `P : Y.Z → Prop` to `fun y => ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔠 : GMem X₁ z₁ act V ev X t δ) (ξc : Sp V ⟶ Y.Z), ξc ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z …`.

Establish `step : ∀ a b : Y.Z, πY a = z₁ → πY b = z₁ → a ⤳ b → (P a ↔ P b)`. Introduce `a b ha hb hab`. Take `⟨Va, _, _, _, _, eva, Xa, _, ta, δa, 𝔠a, ξa, hξa, hca, -⟩` from `GlobalTheory.T.exists_thetaMember_through_model_point I X₁ z₁ act hact Y πY hY a ha`. Take `⟨Vb, _, _, _, _, evb, Xb, _, tb, δb, 𝔠b, ξb, hξb, hcb, -⟩` from `GlobalTheory.T.exists_thetaMember_through_model_point I X₁ z₁ act hact Y πY hY b hb`. Prove the components needed by the constructor for the conclusion.

Introduce `hP V _ _ _ _ ev X _ t δ 𝔠 ξc hξc hc`. Establish `h1` using `hP Va eva Xa ta δa 𝔠a ξa hξa hca`. Establish `h2` using `GlobalTheory.T.thetaMembers_lattices_iso_of_specializes_dvr I X₁ z₁ act hact Y πY hY Va eva Xa ta δa 𝔠a ξa V ev X t δ 𝔠 ξc hξa hξc (by rw [hca, hc]; exact hab)`. Conclude with `h1.trans h2`. Introduce `hP V _ _ _ _ ev X _ t δ 𝔠 ξc hξc hc`.

Establish `h1` using `hP Vb evb Xb tb δb 𝔠b ξb hξb hcb`. Establish `h2` using `GlobalTheory.T.thetaMembers_lattices_iso_of_specializes_dvr I X₁ z₁ act hact Y πY hY V ev X t δ 𝔠 ξc Vb evb Xb tb δb 𝔠b ξb hξc hξb (by rw [hc, hcb]; exact hab)`. Conclude with `h1.trans h2.symm`. Establish `key : ∀ y y' : Y.Z, Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' → (P y ↔ P y')`. Introduce `y y' h`.

Proceed by induction on `h with`. Consider the case `rel a b hr => exact step a b hr.1 hr.2.1 hr.2.2`. Consider the case `refl => exact Iff.rfl`. Consider the case `symm _ _ _ ih => exact ih.symm`. Consider the case `trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2`.

Use `haveI := 𝔫₀.loc`. Use `haveI := 𝔫₁.loc`. Establish `c₀ : πY (ξ₀ (closedPoint W₀)) = z₁` using `closed_over hξ₀`. Establish `c₁ : πY (ξ₁ (closedPoint W₁)) = z₁` using `closed_over hξ₁`. Establish `P0 : P (ξ₀ (closedPoint W₀))`.

Introduce `V _ _ _ _ ev X _ t δ 𝔠 ξc hξc hc`. Conclude with `GlobalTheory.T.thetaMembers_lattices_iso_of_specializes_dvr I X₁ z₁ act hact Y πY hY W₀ e₀ X₀ s₀ δ₀ 𝔫₀ ξ₀ V ev X t δ 𝔠 ξc hξ₀ hξc (by rw [hc])`. Establish `P1` using `(key _ _ (GlobalTheory.T.fibre_points_joined_by_specialisation_chain X₁ z₁ Y πY hY _ _ c₀ c₁)).1 P0`. Conclude with `a₀.trans ((P1 W₁ e₁ X s₁ δ 𝔫₁ ξ₁ hξ₁ rfl).trans a₁.symm)`.
-/
theorem latTo_all (hact : IsAct X₁ act)
    {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {t₀ : X₀ → V₀} {δ₀ : I → X₀ → X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪₀ : GMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (𝔪 : GMem X₁ z₁ act V ev X t δ) : 𝔪₀.LatTo 𝔪 := by
  obtain ⟨Y, πY, hY⟩ := GlobalTheory.T.exists_semiAbelianExtendingModel_above_thetaSystem X₁
  have lift : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
      {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
      (𝔪 : GMem X₁ z₁ act V ev X t δ), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
        (_ : IsDiscreteValuationRing V') (ev' : X₁.M.Z.presheaf.stalk z₁ →+* V') (t' : X → V')
        (𝔫 : GMem X₁ z₁ act V' ev' X t' δ) (ξ : Sp V' ⟶ Y.Z),
        ξ ≫ πY = spMap ev' ≫ X₁.M.Z.fromSpecStalk z₁ ∧ 𝔪.LatTo 𝔫 := by
    intro V _ _ _ ev X _ t δ 𝔪
    obtain ⟨V₁, _, _, _, _, j₁, hcn₁, hj₁, hl₁⟩ := GlobalTheory.CompleteNormalDvr.exists_dvr_isCN V 𝔪.cn
    haveI := 𝔪.loc
    haveI := hl₁
    obtain ⟨V₂, _, _, _, _, j₂, ξ, hcn₂, hj₂, hl₂, hξ⟩ :=
      GlobalTheory.T.exists_trait_lift_to_semiAbelianModel X₁ z₁ Y πY hY V₁ (j₁.comp ev) inferInstance hcn₁
    haveI := hl₂
    have hj : Function.Injective (j₂.comp j₁) := hj₂.comp hj₁
    obtain ⟨𝔫, -, hyy⟩ := GlobalTheory.T.uniformisedMember_baseChange_injective_localHom I X₁ z₁ act V ev X t δ 𝔪 V₂ (j₂.comp j₁)
      (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₂) hj) hcn₂ hj inferInstance
      (fun v => IsLocalization.map_eq _ v)
    refine ⟨V₂, inferInstance, inferInstance, inferInstance, inferInstance, (j₂.comp j₁).comp ev, _, 𝔫, ξ, ?_,
      AddEquiv.refl _, fun _ _ => rfl, hyy⟩
    rw [hξ, RingHom.comp_assoc]
  obtain ⟨W₀, _, _, _, _, e₀, s₀, 𝔫₀, ξ₀, hξ₀, a₀⟩ := lift 𝔪₀
  obtain ⟨W₁, _, _, _, _, e₁, s₁, 𝔫₁, ξ₁, hξ₁, a₁⟩ := lift 𝔪
  let P : Y.Z → Prop := fun y => ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X)
    (𝔠 : GMem X₁ z₁ act V ev X t δ) (ξc : Sp V ⟶ Y.Z),
    ξc ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ → ξc (closedPoint V) = y → 𝔫₀.LatTo 𝔠
  have step : ∀ a b : Y.Z, πY a = z₁ → πY b = z₁ → a ⤳ b → (P a ↔ P b) := by
    intro a b ha hb hab
    obtain ⟨Va, _, _, _, _, eva, Xa, _, ta, δa, 𝔠a, ξa, hξa, hca, -⟩ := GlobalTheory.T.exists_thetaMember_through_model_point I X₁ z₁ act hact Y πY hY a ha
    obtain ⟨Vb, _, _, _, _, evb, Xb, _, tb, δb, 𝔠b, ξb, hξb, hcb, -⟩ := GlobalTheory.T.exists_thetaMember_through_model_point I X₁ z₁ act hact Y πY hY b hb
    constructor
    · intro hP V _ _ _ _ ev X _ t δ 𝔠 ξc hξc hc
      have h1 := hP Va eva Xa ta δa 𝔠a ξa hξa hca
      have h2 := GlobalTheory.T.thetaMembers_lattices_iso_of_specializes_dvr I X₁ z₁ act hact Y πY hY Va eva Xa ta δa 𝔠a ξa V ev X t δ 𝔠 ξc hξa hξc
        (by rw [hca, hc]; exact hab)
      exact h1.trans h2
    · intro hP V _ _ _ _ ev X _ t δ 𝔠 ξc hξc hc
      have h1 := hP Vb evb Xb tb δb 𝔠b ξb hξb hcb
      have h2 := GlobalTheory.T.thetaMembers_lattices_iso_of_specializes_dvr I X₁ z₁ act hact Y πY hY V ev X t δ 𝔠 ξc Vb evb Xb tb δb 𝔠b ξb hξc hξb
        (by rw [hc, hcb]; exact hab)
      exact h1.trans h2.symm
  have key : ∀ y y' : Y.Z, Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' → (P y ↔ P y') := by
    intro y y' h
    induction h with
    | rel a b hr => exact step a b hr.1 hr.2.1 hr.2.2
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  haveI := 𝔫₀.loc
  haveI := 𝔫₁.loc
  have c₀ : πY (ξ₀ (closedPoint W₀)) = z₁ := closed_over hξ₀
  have c₁ : πY (ξ₁ (closedPoint W₁)) = z₁ := closed_over hξ₁
  have P0 : P (ξ₀ (closedPoint W₀)) := by
    intro V _ _ _ _ ev X _ t δ 𝔠 ξc hξc hc
    exact GlobalTheory.T.thetaMembers_lattices_iso_of_specializes_dvr I X₁ z₁ act hact Y πY hY W₀ e₀ X₀ s₀ δ₀ 𝔫₀ ξ₀ V ev X t δ 𝔠 ξc hξ₀ hξc (by rw [hc])
  have P1 := (key _ _ (GlobalTheory.T.fibre_points_joined_by_specialisation_chain X₁ z₁ Y πY hY _ _ c₀ c₁)).1 P0
  exact a₀.trans ((P1 W₁ e₁ X s₁ δ 𝔫₁ ξ₁ hξ₁ rfl).trans a₁.symm)

/- English proof (translation)
Introduce `I X₁ z₁ act hact V₀ _ _ _ ev₀ X₀ _ t₀ δ₀ 𝔪₀ V _ _ _ ev X _ t δ 𝔪`. Conclude with `latTo_all hact 𝔪₀ 𝔪`.
-/
theorem exists_latTo_of_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] (ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀) (X₀ : Type) [AddCommGroup X₀] (t₀ : X₀ → V₀) (δ₀ : I → X₀ → X₀) (𝔪₀ : GlobalTheory.GSep.GMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔪₀.LatTo 𝔪 := by
  intro I X₁ z₁ act hact V₀ _ _ _ ev₀ X₀ _ t₀ δ₀ 𝔪₀ V _ _ _ ev X _ t δ 𝔪
  exact latTo_all hact 𝔪₀ 𝔪

end GlobalTheory.GSep.Cmp
