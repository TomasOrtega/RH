import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberOfRefinedUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliTraitPeriodsMonomialPosDefStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Cmp.Thru

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

Establish `hemb : ∀ r, emb (M.stalkHom z r) = algebraMap V₀ (FractionRing V₀) (φ₀ r)` using `fun r => IsFractionRing.lift_algebraMap (A := M.Z.presheaf.stalk z) hg₀ r`. Use `⟨V₀, inferInstance, inferInstance, hdvr, φ₀, emb, hcpl, hchar, hl, ?_⟩` and prove the remaining obligations. Rewrite using `[← spMap_stalkHom, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Rewrite using `[show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap]`.

Use `congr 1`. Use extensionality with `r`. Conclude with `(hemb r).symm`.
-/
theorem exists_cdvr_thru {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] [CharZero Ω]
    (M : RatModel o Ω) (z : M.Z) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : M.Z.presheaf.stalk z →+* V)
      (e : Ω →+* FractionRing V), IsAdicComplete (maximalIdeal V) V ∧ CharZero V ∧ IsLocalHom φ ∧
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
  refine ⟨V₀, inferInstance, inferInstance, hdvr, φ₀, emb, hcpl, hchar, hl, ?_⟩
  rw [← spMap_stalkHom, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap]
  congr 1
  ext r
  exact (hemb r).symm

/- English proof (translation)
Introduce `g n F W Z i X₁ z₁ act hact Y πY hY y hy`. Substitute `hy` using the available equality. Take `⟨U₀, EE, -, -, -, hhom, -⟩` from `hY`. Use `haveI := X₁.imm`. Use `haveI : CharZero X₁.Ω₁ := X₁.ar.char`.

Use `haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded`. Take `⟨V₀, _, _, hdvr, φ₀, emb, hcpl, hchar, hl₀, hptY⟩` from `exists_cdvr_thru Y y`. Establish `hB : GlobalTheory.Mum.Base V₀` using `⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hchar⟩`. Establish `hπ : Y.pt ≫ πY = X₁.M.pt`. Use `Eq.trans hhom ?_` and prove the remaining obligations.

Conclude with `(congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _)`. Set `s : X₁.M.Z.presheaf.stalk (πY y) →+* Y.Z.presheaf.stalk y` to `(πY.stalkMap y).hom`. Establish `hs : spMap s ≫ X₁.M.Z.fromSpecStalk (πY y) = Y.Z.fromSpecStalk y ≫ πY` using `Scheme.SpecMap_stalkMap_fromSpecStalk πY`. Use `haveI hsl : IsLocalHom s := inferInstanceAs (IsLocalHom (πY.stalkMap y).hom)`. Set `y₀ : Sp (FractionRing V₀) ⟶ F.X` to `spMap emb ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u`.

Take `⟨T, f, fK, hf, hfl, hff, hfK, hTy⟩` from `GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ (zetaAway n) F V₀ hB hdvr y₀`. Use `haveI := hfl`. Set `ψ : Y.Z.presheaf.stalk y →+* T.V` to `f.comp φ₀`. Set `ev : X₁.M.Z.presheaf.stalk (πY y) →+* T.V` to `ψ.comp s`. Establish `hξ : (spMap ψ ≫ Y.Z.fromSpecStalk y) ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y)`.

Rewrite using `[Category.assoc, ← hs, ← Category.assoc, spMap_spMap]`. Establish `hkey : jK T.V ≫ spMap ψ = spMap fK ≫ jK V₀ ≫ spMap φ₀`. Rewrite using `[show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl, show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap, spMap_spMap]`. Use `congr 1`. Use extensionality with `a`.

Simplify using `only [RingHom.comp_apply]`. Conclude with `(hfK _).symm`. Establish `hpt' : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = spMap fK ≫ spMap emb ≫ X₁.M.pt`. Rewrite using `[← hξ, ← hπ, ← Category.assoc (spMap emb), ← hptY, Category.assoc (spMap ψ), ← Category.assoc (jK T.V), hkey]`. Simplify using `only [Category.assoc]`.

Establish `hreg : RegAt X₁ (πY y) ev`. Introduce `a _`. Rewrite using `[hpt']`. Express the relevant statement in the definitionally equal form `a ∈ X₁.M.O (X₁.M.pt ((spMap fK ≫ spMap emb) (closedPoint (FractionRing T.V))))`. Rewrite using `[X₁.M.pt_apply, RatModel.O_genericPoint]`.

Discharge the goal by the elementary cases of `trivial`. Establish `hcomm : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) ≫ X₁.π = T.y ≫ i`. Use `congrArg (· ≫ X₁.π) hpt'` as an intermediate fact. Simplify using `only [Category.assoc] at this`. Rewrite using `[this, hTy, X₁.comp]`.

Simplify using `only [y₀, Category.assoc]`. Take `⟨hmono, hnn, -, -⟩` from `GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ (zetaAway n) F T`. Establish `hCN : IsCN T.V` using `⟨inferInstance, inferInstance, T.complete, inferInstance⟩`. Use `haveI hψ : IsLocalHom ψ := RingHom.isLocalHom_comp _ _`. Take `⟨𝔪, -⟩` from `GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation g X₁.one_le n X₁.three_le X₁.odd F Z X₁.z i X₁.proj (fun x => ⟨X₁.normalZ.isDomain_stalk x, X₁.normalZ.isIntegrallyClosed_stalk x⟩) X₁.thetaSetup_structureMap_comp X₁.dense W X₁.e8 X₁.thetaInt X₁ (πY y) act hact T …`.

Use `⟨T.V, inferInstance, inferInstance, inferInstance, inferInstance, ev, _, inferInstance, 1, _, _, 𝔪, spMap ψ ≫ Y.Z.fromSpecStalk y, hξ, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Y.Z.fromSpecStalk y (spMap ψ (closedPoint T.V)) = y`. Establish `: spMap ψ (closedPoint T.V) = closedPoint (Y.Z.presheaf.stalk y)` using `IsLocalRing.comap_closedPoint ψ`. Rewrite using `[this]`. Conclude with `Scheme.fromSpecStalk_closedPoint`.
-/
theorem exists_uMem_thru : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y : Y.Z, πY y = z₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsDiscreteValuationRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V ev X t δ) (ξ : Sp V ⟶ Y.Z), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ∧ ξ (closedPoint V) = y := by
  intro g n F W Z i X₁ z₁ act hact Y πY hY y hy
  subst hy
  obtain ⟨U₀, EE, -, -, -, hhom, -⟩ := hY
  haveI := X₁.imm
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  obtain ⟨V₀, _, _, hdvr, φ₀, emb, hcpl, hchar, hl₀, hptY⟩ := exists_cdvr_thru Y y
  have hB : GlobalTheory.Mum.Base V₀ := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hchar⟩
  have hπ : Y.pt ≫ πY = X₁.M.pt := by
    refine Eq.trans hhom ?_
    exact (congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  let s : X₁.M.Z.presheaf.stalk (πY y) →+* Y.Z.presheaf.stalk y := (πY.stalkMap y).hom
  have hs : spMap s ≫ X₁.M.Z.fromSpecStalk (πY y) = Y.Z.fromSpecStalk y ≫ πY :=
    Scheme.SpecMap_stalkMap_fromSpecStalk πY
  haveI hsl : IsLocalHom s := inferInstanceAs (IsLocalHom (πY.stalkMap y).hom)
  let y₀ : Sp (FractionRing V₀) ⟶ F.X := spMap emb ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u
  obtain ⟨T, f, fK, hf, hfl, hff, hfK, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ (zetaAway n) F V₀ hB hdvr y₀
  haveI := hfl
  let ψ : Y.Z.presheaf.stalk y →+* T.V := f.comp φ₀
  let ev : X₁.M.Z.presheaf.stalk (πY y) →+* T.V := ψ.comp s
  have hξ : (spMap ψ ≫ Y.Z.fromSpecStalk y) ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) := by
    rw [Category.assoc, ← hs, ← Category.assoc, spMap_spMap]
  have hkey : jK T.V ≫ spMap ψ = spMap fK ≫ jK V₀ ≫ spMap φ₀ := by
    rw [show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl,
      show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap, spMap_spMap]
    congr 1
    ext a
    simp only [RingHom.comp_apply]
    exact (hfK _).symm
  have hpt' : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = spMap fK ≫ spMap emb ≫ X₁.M.pt := by
    rw [← hξ, ← hπ, ← Category.assoc (spMap emb), ← hptY, Category.assoc (spMap ψ), ← Category.assoc (jK T.V), hkey]
    simp only [Category.assoc]
  have hreg : RegAt X₁ (πY y) ev := by
    intro a _
    rw [hpt']
    change a ∈ X₁.M.O (X₁.M.pt ((spMap fK ≫ spMap emb) (closedPoint (FractionRing T.V))))
    rw [X₁.M.pt_apply, RatModel.O_genericPoint]
    trivial
  have hcomm : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) ≫ X₁.π = T.y ≫ i := by
    have := congrArg (· ≫ X₁.π) hpt'
    simp only [Category.assoc] at this
    rw [this, hTy, X₁.comp]
    simp only [y₀, Category.assoc]
  obtain ⟨hmono, hnn, -, -⟩ := GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ (zetaAway n) F T
  have hCN : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  haveI hψ : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
  obtain ⟨𝔪, -⟩ := GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation g X₁.one_le n X₁.three_le X₁.odd F Z X₁.z i X₁.proj
    (fun x => ⟨X₁.normalZ.isDomain_stalk x, X₁.normalZ.isIntegrallyClosed_stalk x⟩) X₁.thetaSetup_structureMap_comp X₁.dense W X₁.e8
    X₁.thetaInt X₁ (πY y) act hact T.V
    (Wit.ofDeg T.D.toPre T.D.tau_bimult) 1 ![T.ϖ] ![T.β] (fun k => by fin_cases k; exact T.irr.ne_zero)
    (fun k a b => by fin_cases k; exact T.symm a b) (fun k a => by fin_cases k; exact hnn a) hmono T.V (RingHom.id _)
    hCN Function.injective_id (RingHom.Finite.id T.V) T.D (AddEquiv.refl _) (Wit.refines_ofDeg _ _) T.G T.A T.U T.y T.α T.α₂
    T.semi T.cart T.sq T.lb ev (RingHom.isLocalHom_comp _ _) hreg hcomm
  refine ⟨T.V, inferInstance, inferInstance, inferInstance, inferInstance, ev, _, inferInstance, 1, _, _, 𝔪,
    spMap ψ ≫ Y.Z.fromSpecStalk y, hξ, ?_⟩
  change Y.Z.fromSpecStalk y (spMap ψ (closedPoint T.V)) = y
  have : spMap ψ (closedPoint T.V) = closedPoint (Y.Z.presheaf.stalk y) := IsLocalRing.comap_closedPoint ψ
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.Poinc.Sep.Cmp.Thru
