import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinModelGenericFibreIsPullbackThetaSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationAtCompleteTraitOfModelStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverPullbackSemiAbelianModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.Thru

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Establish `h1` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt`. Establish `h2` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)`. Use `Eq.trans ?_ h1` and prove the remaining obligations. Rewrite using `[← h2, ← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_stalkHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    spMap (M.stalkHom z) ≫ M.Z.fromSpecStalk z = M.pt := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine Eq.trans ?_ h1
  rw [← h2, ← Category.assoc, ← Spec.map_comp]
  rfl

/- English proof (translation)
Use `letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra`. Establish `: FaithfulSMul (M.Z.presheaf.stalk z) Ω` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (M.stalkHom_injective z)`. Use `IsFractionRing.of_field _ _ fun x => ?_` and prove the remaining obligations. Take `⟨a, b, -, hx⟩` from `IsFractionRing.div_surjective (A := M.O z) x`. Use `⟨(M.stalkEquiv z).symm a, (M.stalkEquiv z).symm b, ?_⟩` and prove the remaining obligations.

Establish `h : ∀ c : M.O z, algebraMap (M.Z.presheaf.stalk z) Ω ((M.stalkEquiv z).symm c) = c` using `fun c => by`. Express the relevant statement in the definitionally equal form `M.stalkHom z _ = _`. Rewrite using `[← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]`. Rewrite using `[h, h, ← hx]`. Both sides reduce to the same expression.
-/
theorem isFractionRing_stalk {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
    IsFractionRing (M.Z.presheaf.stalk z) Ω := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  have : FaithfulSMul (M.Z.presheaf.stalk z) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M.stalkHom_injective z)
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M.O z) x
  refine ⟨(M.stalkEquiv z).symm a, (M.stalkEquiv z).symm b, ?_⟩
  have h : ∀ c : M.O z, algebraMap (M.Z.presheaf.stalk z) Ω ((M.stalkEquiv z).symm c) = c := fun c => by
    change M.stalkHom z _ = _
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  rw [h, h, ← hx]
  rfl

/- English proof (translation)
Use `letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra`. Use `haveI := isFractionRing_stalk M z`. Use `haveI : CharZero (M.Z.presheaf.stalk z) := (M.stalkHom z).charZero`. Use `haveI := M.lft`. Use `haveI : IsLocallyNoetherian (Sp o) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of o)))`.

Use `haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s`. Take `⟨V₀, _, _, _, φ₀, ⟨hdvr, hcpl, hchar⟩, hinj₀, hmax⟩` from `GlobalTheory.ClosedPol.exists_cdvr (M.Z.presheaf.stalk z) (maximalIdeal _)`. Establish `hl : IsLocalHom φ₀` using `((IsLocalRing.local_hom_TFAE φ₀).out 0 4).2 hmax`. Establish `hg₀ : Function.Injective ((algebraMap V₀ (FractionRing V₀)).comp φ₀)` using `(IsFractionRing.injective V₀ (FractionRing V₀)).comp hinj₀`. Set `emb : Ω →+* FractionRing V₀` to `IsFractionRing.lift (A := M.Z.presheaf.stalk z) hg₀`.

Establish `hemb : ∀ r, emb (M.stalkHom z r) = algebraMap V₀ (FractionRing V₀) (φ₀ r)` using `fun r => IsFractionRing.lift_algebraMap (A := M.Z.presheaf.stalk z) hg₀ r`. Use `⟨V₀, inferInstance, inferInstance, hdvr, φ₀, emb, hcpl, hchar, hl, hemb, ?_⟩` and prove the remaining obligations. Rewrite using `[← spMap_stalkHom, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Rewrite using `[show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap]`.

Use `congr 1`. Use extensionality with `r`. Conclude with `(hemb r).symm`.
-/
theorem exists_cdvr_thru {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] [CharZero Ω]
    (M : RatModel o Ω) (z : M.Z) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : M.Z.presheaf.stalk z →+* V)
      (e : Ω →+* FractionRing V), IsAdicComplete (maximalIdeal V) V ∧ CharZero V ∧ IsLocalHom φ ∧
      (∀ r, e (M.stalkHom z r) = algebraMap V (FractionRing V) (φ r)) ∧
      jK V ≫ spMap φ ≫ M.Z.fromSpecStalk z = spMap e ≫ M.pt := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  haveI := isFractionRing_stalk M z
  haveI : CharZero (M.Z.presheaf.stalk z) := (M.stalkHom z).charZero
  haveI := M.lft
  haveI : IsLocallyNoetherian (Sp o) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of o)))
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨V₀, _, _, _, φ₀, ⟨hdvr, hcpl, hchar⟩, hinj₀, hmax⟩ :=
    GlobalTheory.ClosedPol.exists_cdvr (M.Z.presheaf.stalk z) (maximalIdeal _)
  have hl : IsLocalHom φ₀ := ((IsLocalRing.local_hom_TFAE φ₀).out 0 4).2 hmax
  have hg₀ : Function.Injective ((algebraMap V₀ (FractionRing V₀)).comp φ₀) :=
    (IsFractionRing.injective V₀ (FractionRing V₀)).comp hinj₀
  let emb : Ω →+* FractionRing V₀ := IsFractionRing.lift (A := M.Z.presheaf.stalk z) hg₀
  have hemb : ∀ r, emb (M.stalkHom z r) = algebraMap V₀ (FractionRing V₀) (φ₀ r) := fun r =>
    IsFractionRing.lift_algebraMap (A := M.Z.presheaf.stalk z) hg₀ r
  refine ⟨V₀, inferInstance, inferInstance, hdvr, φ₀, emb, hcpl, hchar, hl, hemb, ?_⟩
  rw [← spMap_stalkHom, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap]
  congr 1
  ext r
  exact (hemb r).symm

/- English proof (translation)
Introduce `I X₁ z₁ act hact Y πY hY V _ _ _ hcpl hchar ev hev ξ e hξ hjξ`. Take `⟨U₀, EE, ⟨O⟩, hO, -, hhom, -⟩` from `hY`. Establish `hπ : Y.pt ≫ πY = X₁.M.pt` using `hhom.trans ((congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _))`. Take `⟨ψ, hψ, hψL, hψE⟩` from `GlobalTheory.T.zarhinModel_genericFibre_isPullback_thetaSystem X₁ Y U₀ EE O hO`. Establish `hab : (ξ ⁻¹' abLocus O.G).Nonempty`.

Use `⟨jK V (closedPoint (FractionRing V)), ?_⟩` and prove the remaining obligations. Establish `e1 : ξ (jK V (closedPoint (FractionRing V))) = Y.pt (spMap e (closedPoint (FractionRing V)))` using `congrArg (fun f : Sp (FractionRing V) ⟶ Y.Z => f (closedPoint (FractionRing V))) hjξ`. Rewrite using `[Set.mem_preimage, e1]`. Conclude with `GlobalTheory.Mum.CoverPull.pt_mem_abLocus _ _ X₁.S X₁.ρ Y U₀ EE hO O _`. Take `⟨D, A, U, β, hβ, hβL, hβE⟩` from `GlobalTheory.T.exists_uniformisation_at_completeTrait_of_model X₁ Y U₀ EE O V hcpl hchar ξ e hjξ hab`.

Establish `hpt : jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ = spMap e ≫ X₁.M.pt`. Rewrite using `[← hξ, ← Category.assoc, hjξ, Category.assoc, hπ]`. Establish `hend : ∀ a, ∃ E : EndU U.toUnifPre, E.aA.left ≫ (β ≫ ψ) = (β ≫ ψ) ≫ (act a).left`. Introduce `a`. Take `⟨F, hF, hFψ⟩` from `hψE (act a) (hact a)`.

Take `⟨E, hE⟩` from `hβE F hF`. Use `⟨E, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hE, Category.assoc, hFψ, Category.assoc]`. Use `choose E hE using hend`. Establish `hV : IsCN V` using `⟨inferInstance, inferInstance, hcpl, hchar⟩`.

Establish `hpsi : ∀ mu : D.toPre.X, ∃ r : V, Formalism.L2.Pj.PsiCoord D.toPre mu r` using `fun mu => by`. Take `⟨r, hr, -⟩` from `(PsiCoordLocal.main V D hV.2.1 mu).1`. Conclude with `⟨r, hr⟩`. Use `choose t ht using hpsi`. Take `⟨wl, hwl⟩` from `LBIso.trans A.isLB (pull_isLB (pull_isLB O.L.isLB _) _) (pull_isLB X₁.ρ.P.isLB _) hβL (lbIso_pull_comp hψL β)`.

Use `⟨D.toPre.X, inferInstance, t, fun a => (E a).h, ⟨{ cn := hV loc := hev reg := fun a _ => ?_ yK := e.comp X₁.S.R.val.toRingHom yK_eq := fun a => ?_ D := D e₈ := AddEquiv.refl _ G := (Over.pullback ξ).obj O.G semi := IsSemiAbelian.pullback _ _ O.semi A := A U := U φ := β ≫ ψ cart : …` and prove the remaining obligations. Rewrite using `[hpt]`. Express the relevant statement in the definitionally equal form `a ∈ X₁.M.O (X₁.M.pt ((spMap e) (closedPoint (FractionRing V))))`. Rewrite using `[X₁.M.pt_apply, RatModel.O_genericPoint]`. Discharge the goal by the elementary cases of `trivial`.

Rewrite using `[hpt, GlobalTheory.FieldPts.val_spMap, RatModel.val_pt]`. Both sides reduce to the same expression.
-/
theorem exists_gMem_of_trait : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → CharZero V → ∀ (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → ∀ (ξ : Sp V ⟶ Y.Z) (e : X₁.Ω₁ →+* FractionRing V), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ → jK V ≫ ξ = spMap e ≫ Y.pt → ∃ (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  intro I X₁ z₁ act hact Y πY hY V _ _ _ hcpl hchar ev hev ξ e hξ hjξ
  obtain ⟨U₀, EE, ⟨O⟩, hO, -, hhom, -⟩ := hY
  have hπ : Y.pt ≫ πY = X₁.M.pt :=
    hhom.trans ((congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _))
  obtain ⟨ψ, hψ, hψL, hψE⟩ := GlobalTheory.T.zarhinModel_genericFibre_isPullback_thetaSystem X₁ Y U₀ EE O hO
  have hab : (ξ ⁻¹' abLocus O.G).Nonempty := by
    refine ⟨jK V (closedPoint (FractionRing V)), ?_⟩
    have e1 : ξ (jK V (closedPoint (FractionRing V))) = Y.pt (spMap e (closedPoint (FractionRing V))) :=
      congrArg (fun f : Sp (FractionRing V) ⟶ Y.Z => f (closedPoint (FractionRing V))) hjξ
    rw [Set.mem_preimage, e1]
    exact GlobalTheory.Mum.CoverPull.pt_mem_abLocus _ _ X₁.S X₁.ρ Y U₀ EE hO O _
  obtain ⟨D, A, U, β, hβ, hβL, hβE⟩ := GlobalTheory.T.exists_uniformisation_at_completeTrait_of_model X₁ Y U₀ EE O V hcpl hchar ξ e hjξ hab
  have hpt : jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ = spMap e ≫ X₁.M.pt := by
    rw [← hξ, ← Category.assoc, hjξ, Category.assoc, hπ]
  have hend : ∀ a, ∃ E : EndU U.toUnifPre, E.aA.left ≫ (β ≫ ψ) = (β ≫ ψ) ≫ (act a).left := by
    intro a
    obtain ⟨F, hF, hFψ⟩ := hψE (act a) (hact a)
    obtain ⟨E, hE⟩ := hβE F hF
    refine ⟨E, ?_⟩
    rw [← Category.assoc, hE, Category.assoc, hFψ, Category.assoc]
  choose E hE using hend
  have hV : IsCN V := ⟨inferInstance, inferInstance, hcpl, hchar⟩
  have hpsi : ∀ mu : D.toPre.X, ∃ r : V, Formalism.L2.Pj.PsiCoord D.toPre mu r := fun mu => by
    obtain ⟨r, hr, -⟩ := (PsiCoordLocal.main V D hV.2.1 mu).1
    exact ⟨r, hr⟩
  choose t ht using hpsi
  obtain ⟨wl, hwl⟩ := LBIso.trans A.isLB (pull_isLB (pull_isLB O.L.isLB _) _) (pull_isLB X₁.ρ.P.isLB _) hβL
    (lbIso_pull_comp hψL β)
  refine ⟨D.toPre.X, inferInstance, t, fun a => (E a).h, ⟨{
    cn := hV
    loc := hev
    reg := fun a _ => ?_
    yK := e.comp X₁.S.R.val.toRingHom
    yK_eq := fun a => ?_
    D := D
    e₈ := AddEquiv.refl _
    G := (Over.pullback ξ).obj O.G
    semi := IsSemiAbelian.pullback _ _ O.semi
    A := A
    U := U
    φ := β ≫ ψ
    cart := (hβ.comp hψ).congr (spMap_spMap e X₁.S.R.val.toRingHom) rfl
    wl := wl
    wl_gen := hwl
    equiv := fun a => ⟨E a, hE a, fun _ => rfl⟩
    psi := fun mu => ⟨1, by simpa using ht mu⟩ }⟩⟩
  · rw [hpt]
    change a ∈ X₁.M.O (X₁.M.pt ((spMap e) (closedPoint (FractionRing V))))
    rw [X₁.M.pt_apply, RatModel.O_genericPoint]
    trivial
  · rw [hpt, GlobalTheory.FieldPts.val_spMap, RatModel.val_pt]
    rfl

/- English proof (translation)
Introduce `I X₁ z₁ act hact Y πY hY y hy`. Substitute `hy` using the available equality. Use `haveI : CharZero X₁.Ω₁ := X₁.ar.char`. Use `haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded`. Take `⟨V, _, _, hdvr, φ₀, emb, hcpl, hchar, hl₀, -, hptY⟩` from `exists_cdvr_thru Y y`.

Establish `hπ : Y.pt ≫ πY = X₁.M.pt`. Take `⟨-, -, -, -, -, hhom, -⟩` from `hY`. Use `Eq.trans hhom ?_` and prove the remaining obligations. Conclude with `(congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _)`. Set `s : X₁.M.Z.presheaf.stalk (πY y) →+* Y.Z.presheaf.stalk y` to `(πY.stalkMap y).hom`.

Establish `hs : spMap s ≫ X₁.M.Z.fromSpecStalk (πY y) = Y.Z.fromSpecStalk y ≫ πY` using `Scheme.SpecMap_stalkMap_fromSpecStalk πY`. Use `haveI hsl : IsLocalHom s := inferInstanceAs (IsLocalHom (πY.stalkMap y).hom)`. Set `ev : X₁.M.Z.presheaf.stalk (πY y) →+* V` to `φ₀.comp s`. Establish `hξ : (spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y)`. Rewrite using `[Category.assoc, ← hs, ← Category.assoc, spMap_spMap]`.

Establish `hjξ : jK V ≫ spMap φ₀ ≫ Y.Z.fromSpecStalk y = spMap emb ≫ Y.pt` using `hptY`. Establish `hpt' : jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = spMap emb ≫ X₁.M.pt`. Combine the equalities or inequalities in the displayed calculation. Establish `hinj : Function.Injective ev`. Establish `h1 : spMap ((algebraMap V (FractionRing V)).comp ev) ≫ X₁.M.Z.fromSpecStalk (πY y) = spMap (emb.comp (X₁.M.stalkHom (πY y))) ≫ X₁.M.Z.fromSpecStalk (πY y)`.

Rewrite using `[← spMap_spMap (algebraMap V (FractionRing V)) ev, ← spMap_spMap emb (X₁.M.stalkHom (πY y)), Category.assoc, Category.assoc, spMap_stalkHom]`. Conclude with `hpt'`. Establish `h2` using `(cancel_mono _).1 h1`. Establish `h3 : (algebraMap V (FractionRing V)).comp ev = emb.comp (X₁.M.stalkHom (πY y))` using `congrArg CommRingCat.Hom.hom (Spec.map_injective h2)`. Introduce `a b hab`.

Apply `X₁.M.stalkHom_injective` to reduce the goal to its premises. Apply `emb.injective` to reduce the goal to its premises. Establish `ha` using `RingHom.congr_fun h3 a`. Establish `hb` using `RingHom.congr_fun h3 b`. Simplify using `only [RingHom.comp_apply] at ha hb`.

Rewrite using `[← ha, ← hb, hab]`. Take `⟨X, _, t, δ, ⟨𝔫⟩⟩` from `exists_gMem_of_trait I X₁ (πY y) act hact Y πY hY V hcpl hchar ev (RingHom.isLocalHom_comp _ _) _ emb hξ hjξ`. Use `⟨V, inferInstance, inferInstance, inferInstance, hdvr, ev, X, inferInstance, t, δ, 𝔫, spMap φ₀ ≫ Y.Z.fromSpecStalk y, hξ, ?_, hinj⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Y.Z.fromSpecStalk y (spMap φ₀ (closedPoint V)) = y`. Establish `: spMap φ₀ (closedPoint V) = closedPoint (Y.Z.presheaf.stalk y)` using `IsLocalRing.comap_closedPoint φ₀`.

Rewrite using `[this]`. Conclude with `Scheme.fromSpecStalk_closedPoint`.
-/
theorem exists_gMem_thru : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ y : Y.Z, πY y = z₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsDiscreteValuationRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X) (𝔫 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (ξ : Sp V ⟶ Y.Z), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ∧ ξ (closedPoint V) = y ∧ Function.Injective ev := by
  intro I X₁ z₁ act hact Y πY hY y hy
  subst hy
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  obtain ⟨V, _, _, hdvr, φ₀, emb, hcpl, hchar, hl₀, -, hptY⟩ := exists_cdvr_thru Y y
  have hπ : Y.pt ≫ πY = X₁.M.pt := by
    obtain ⟨-, -, -, -, -, hhom, -⟩ := hY
    refine Eq.trans hhom ?_
    exact (congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  let s : X₁.M.Z.presheaf.stalk (πY y) →+* Y.Z.presheaf.stalk y := (πY.stalkMap y).hom
  have hs : spMap s ≫ X₁.M.Z.fromSpecStalk (πY y) = Y.Z.fromSpecStalk y ≫ πY :=
    Scheme.SpecMap_stalkMap_fromSpecStalk πY
  haveI hsl : IsLocalHom s := inferInstanceAs (IsLocalHom (πY.stalkMap y).hom)
  let ev : X₁.M.Z.presheaf.stalk (πY y) →+* V := φ₀.comp s
  have hξ : (spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) := by
    rw [Category.assoc, ← hs, ← Category.assoc, spMap_spMap]
  have hjξ : jK V ≫ spMap φ₀ ≫ Y.Z.fromSpecStalk y = spMap emb ≫ Y.pt := hptY
  have hpt' : jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = spMap emb ≫ X₁.M.pt := by
    calc jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = jK V ≫ (spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY := by rw [hξ]
      _ = (jK V ≫ spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY := by simp only [Category.assoc]
      _ = (spMap emb ≫ Y.pt) ≫ πY := by rw [hjξ]
      _ = spMap emb ≫ X₁.M.pt := by rw [Category.assoc, hπ]
  have hinj : Function.Injective ev := by
    have h1 : spMap ((algebraMap V (FractionRing V)).comp ev) ≫ X₁.M.Z.fromSpecStalk (πY y) =
        spMap (emb.comp (X₁.M.stalkHom (πY y))) ≫ X₁.M.Z.fromSpecStalk (πY y) := by
      rw [← spMap_spMap (algebraMap V (FractionRing V)) ev, ← spMap_spMap emb (X₁.M.stalkHom (πY y)), Category.assoc,
        Category.assoc, spMap_stalkHom]
      exact hpt'
    have h2 := (cancel_mono _).1 h1
    have h3 : (algebraMap V (FractionRing V)).comp ev = emb.comp (X₁.M.stalkHom (πY y)) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    intro a b hab
    apply X₁.M.stalkHom_injective
    apply emb.injective
    have ha := RingHom.congr_fun h3 a
    have hb := RingHom.congr_fun h3 b
    simp only [RingHom.comp_apply] at ha hb
    rw [← ha, ← hb, hab]
  obtain ⟨X, _, t, δ, ⟨𝔫⟩⟩ := exists_gMem_of_trait I X₁ (πY y) act hact Y πY hY V hcpl hchar ev
    (RingHom.isLocalHom_comp _ _) _ emb hξ hjξ
  refine ⟨V, inferInstance, inferInstance, inferInstance, hdvr, ev, X, inferInstance, t, δ, 𝔫,
    spMap φ₀ ≫ Y.Z.fromSpecStalk y, hξ, ?_, hinj⟩
  change Y.Z.fromSpecStalk y (spMap φ₀ (closedPoint V)) = y
  have : spMap φ₀ (closedPoint V) = closedPoint (Y.Z.presheaf.stalk y) := IsLocalRing.comap_closedPoint φ₀
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.GSep.Thru
