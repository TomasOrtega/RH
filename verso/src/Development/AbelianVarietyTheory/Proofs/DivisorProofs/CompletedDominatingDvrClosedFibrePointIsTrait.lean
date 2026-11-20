import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ _ M G Y α t hαt W hWa x hx hxc F _ β V hV h1 hnu`. Use `haveI := hV`. Set `T` to `AdicCompletion (maximalIdeal V) V`. Set `g : V →+* T` to `algebraMap V T`. Establish `hg : Function.Injective g` using `GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V`.

Set `f : G.left ⟶ Sp R` to `G.hom ≫ M.π`. Set `ρ : R →+* Γ(G.left, W)` to `((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top).hom`. Set `lam : Γ(G.left, W) →+* T` to `g.comp ((β.comp (α.app W).hom).codRestrict V h1)`. Set `φ : R →+* T` to `lam.comp ρ`. Set `ψ : FractionRing R →+* F` to `β.comp ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom`.

Establish `key : ∀ r, β ((α.app W).hom (ρ r)) = ψ (algebraMap R (FractionRing R) r)`. Introduce `r`. Establish `hc : ∀ {a b : Y ⟶ Sp R} (_ : a = b), a.appLE ⊤ (α ⁻¹ᵁ W) le_top = b.appLE ⊤ (α ⁻¹ᵁ W) le_top`. Introduce and unpack `_ _ rfl`. Both sides reduce to the same expression.

Establish `e1 : f.appLE ⊤ W le_top ≫ α.app W = (α ≫ f).appLE ⊤ (α ⁻¹ᵁ W) le_top`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _`. Establish `e2 : α ≫ f = t ≫ jK R`. Simplify using `only [f]`.

Rewrite using `[reassoc_of% hαt, M.gp_π]`. Establish `e4 : (t ≫ jK R).appLE ⊤ (α ⁻¹ᵁ W) le_top = (jK R).appTop ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top` using `Scheme.Hom.comp_appLE t (jK R) ⊤ (α ⁻¹ᵁ W) le_top`. Establish `e3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top`. Rewrite using `[e1, hc e2, e4, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]`. Express the relevant statement in the definitionally equal form `β (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W).hom r) = β ((CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom r)`.

Rewrite using `[e3]`. Establish `hφi : Function.Injective φ`. Introduce `a b hab`. Establish `h2 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ a) = ((β.comp (α.app W).hom).codRestrict V h1) (ρ b)` using `hg hab`. Establish `h3 : β ((α.app W).hom (ρ a)) = β ((α.app W).hom (ρ b))` using `congrArg Subtype.val h2`.

Rewrite `h3` using `[key, key]`. Conclude with `IsFractionRing.injective R (FractionRing R) (ψ.injective h3)`. Use `haveI : CharZero T := charZero_of_injective_ringHom hφi`. Use `⟨T, inferInstance, inferInstance, inferInstance, lam, g, φ, ⟨inferInstance, inferInstance, inferInstance⟩, hg, inferInstance, fun c => rfl, hφi, ?_, ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `r hu`. Assume the negation of the conclusion as `hr`. Establish `hrm : r ∈ maximalIdeal R` using `hr`. Establish `hres : (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom (ρ r)) = 0`. Establish `hb : x ∉ G.left.basicOpen (ρ r)`.

Introduce `hxb`. Establish `e` using `Scheme.basicOpen_appLE f W ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)`. Rewrite `e` using `[basicOpen_eq_of_affine (R := CommRingCat.of R) r]`. Establish `h4` using `((show G.left.basicOpen (ρ r) = _ from e).le hxb).2`. Establish `h7 : r ∉ PrimeSpectrum.asIdeal (f x)` using `h4`.

Establish `h6 : f x = closedPoint R` using `hxc`. Rewrite `h7` using `[h6]`. Conclude with `h7 hrm`. Rewrite `hb` using `[Scheme.mem_basicOpen _ _ _ hx]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 hb`.

Establish `h5` using `hnu (ρ r) hres`. Establish `h6 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ r) ∈ maximalIdeal V` using `(ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h1 (ρ r)⟩)).mp h5`. Conclude with `h6 (isUnit_of_map_unit g _ hu)`. Simplify using `only [Category.assoc]`. Rewrite using `[← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Sp R)) hWa le_top, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]`.

Both sides reduce to the same expression.
-/
theorem trait_at_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), α ≫ G.hom = t ≫ M.gp → ∀ (W : G.left.Opens) (hWa : IsAffineOpen W) (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → ∀ (h1 : ∀ c, β ((α.app W).hom c) ∈ V), (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (lam : Γ(G.left, W) →+* T) (g : V →+* T) (φ : R →+* T), GlobalTheory.LN.CDvr T ∧ Function.Injective g ∧ IsLocalHom g ∧ (∀ c, g ⟨β ((α.app W).hom c), h1 c⟩ = lam c) ∧ Function.Injective φ ∧ IsLocalHom φ ∧ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) ≫ M.π = spMap φ := by
  intro R _ _ _ _ M G Y α t hαt W hWa x hx hxc F _ β V hV h1 hnu
  haveI := hV
  let T := AdicCompletion (maximalIdeal V) V
  let g : V →+* T := algebraMap V T
  have hg : Function.Injective g := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  let f : G.left ⟶ Sp R := G.hom ≫ M.π
  let ρ : R →+* Γ(G.left, W) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top).hom
  let lam : Γ(G.left, W) →+* T := g.comp ((β.comp (α.app W).hom).codRestrict V h1)
  let φ : R →+* T := lam.comp ρ
  let ψ : FractionRing R →+* F :=
    β.comp ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom
  have key : ∀ r, β ((α.app W).hom (ρ r)) = ψ (algebraMap R (FractionRing R) r) := by
    intro r
    have hc : ∀ {a b : Y ⟶ Sp R} (_ : a = b), a.appLE ⊤ (α ⁻¹ᵁ W) le_top = b.appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rintro _ _ rfl; rfl
    have e1 : f.appLE ⊤ W le_top ≫ α.app W = (α ≫ f).appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : α ≫ f = t ≫ jK R := by
      simp only [f]; rw [reassoc_of% hαt, M.gp_π]
    have e4 : (t ≫ jK R).appLE ⊤ (α ⁻¹ᵁ W) le_top = (jK R).appTop ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top :=
      Scheme.Hom.comp_appLE t (jK R) ⊤ (α ⁻¹ᵁ W) le_top
    have e3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W =
        CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          t.appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rw [e1, hc e2, e4, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
    change β (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W).hom r) =
      β ((CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom r)
    rw [e3]
  have hφi : Function.Injective φ := by
    intro a b hab
    have h2 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ a) = ((β.comp (α.app W).hom).codRestrict V h1) (ρ b) := hg hab
    have h3 : β ((α.app W).hom (ρ a)) = β ((α.app W).hom (ρ b)) := congrArg Subtype.val h2
    rw [key, key] at h3
    exact IsFractionRing.injective R (FractionRing R) (ψ.injective h3)
  haveI : CharZero T := charZero_of_injective_ringHom hφi
  refine ⟨T, inferInstance, inferInstance, inferInstance, lam, g, φ,
    ⟨inferInstance, inferInstance, inferInstance⟩, hg, inferInstance, fun c => rfl, hφi, ?_, ?_⟩
  · constructor
    intro r hu
    by_contra hr
    have hrm : r ∈ maximalIdeal R := hr
    have hres : (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom (ρ r)) = 0 := by
      have hb : x ∉ G.left.basicOpen (ρ r) := by
        intro hxb
        have e := Scheme.basicOpen_appLE f W ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
        rw [basicOpen_eq_of_affine (R := CommRingCat.of R) r] at e
        have h4 := ((show G.left.basicOpen (ρ r) = _ from e).le hxb).2
        have h7 : r ∉ PrimeSpectrum.asIdeal (f x) := h4
        have h6 : f x = closedPoint R := hxc
        rw [h6] at h7
        exact h7 hrm
      rw [Scheme.mem_basicOpen _ _ _ hx] at hb
      exact (IsLocalRing.residue_eq_zero_iff _).2 hb
    have h5 := hnu (ρ r) hres
    have h6 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ r) ∈ maximalIdeal V :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h1 (ρ r)⟩)).mp h5
    exact h6 (isUnit_of_map_unit g _ hu)
  · simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Sp R)) hWa le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    rfl

end GlobalTheory.Mum
