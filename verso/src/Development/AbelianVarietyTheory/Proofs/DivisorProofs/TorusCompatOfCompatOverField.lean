import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

/- English proof (translation)
Introduce `o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ X _ m c V _ _ _ ξ a G₁ _ φ₁ h₁ j hext K _ b hb GK _ ψ hψ hK`. Use `haveI hsep : IsSeparated G.hom := hG.separated`. Use `haveI : Flat (splitTorusAff ZU X).hom := (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1`. Use `haveI : Flat (splitTorus (Sp V) X).hom := inferInstanceAs (Flat (pullback.snd _ _))`. Use `haveI : IsSchemeTheoreticallyDominant (spMap b) := GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hb`.

Use `haveI : QuasiCompact (spMap b) := inferInstance`. Use `haveI : IsSchemeTheoreticallyDominant (bcMap (spMap b) X) := IsSchemeTheoreticallyDominant.of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).flip`. Establish `hw : φ₁ ≫ G.hom = G₁.hom ≫ ξ` using `h₁.1.w`. Use `⟨fun e => ?_, fun t => ?_⟩` and prove the remaining obligations. Establish `h1` using `hK.1 e`.

Rewrite `h1` using `[← pullTorus_torusMap_comp]`. Simplify using `only [Category.assoc] at h1`. Establish `e1` using `pullTorus_left hψ j`. Establish `e2` using `pullTorus_left hψ (torusMap (Sp V) (m e) ≫ j)`. Use `GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (bcMap (spMap b) X) ?_` and prove the remaining obligations.

Simplify using `only [Category.assoc, Over.w, hw, Over.w_assoc, Over.comp_left]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨zK, hzK, hvK⟩` from `hK.2 t haveI : NeZero L := ⟨hL.ne'⟩`. Establish `huL : Units.map a.toMonoidHom ζ ^ L = 1` using `by rw [← map_pow, hζ, map_one]`. Set `φh : Multiplicative X →* (Γ(Sp V, ⊤))ˣ` to `{ toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val) map_one' := by simp [unitOn] map_mul' := fun x y => by`.

Simplify using `only [toAdd_mul, map_add, unitOn]`. Rewrite using `[ZMod.val_add, ← pow_eq_pow_mod _ huL, pow_add, map_mul] }`. Set `z : Over.mk (𝟙 (Sp V)) ⟶ splitTorus (Sp V) X` to `(GlobalTheory.splitTorusPointsEquiv (Sp V) X _).symm φh`. Establish `hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val)` using `fun χ => by`. Simplify using `only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]`.

Both sides reduce to the same expression. Establish `hwz : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b`. Rewrite using `[Category.assoc, Over.w z]`. Simplify using the standard rewrite rules. Set `z' : Over.mk (𝟙 (Sp K)) ⟶ splitTorus (Sp K) X` to `Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hwz) ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)`.

Establish `hz' : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left` using `(GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _`. Establish `hcz' : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val)` using `fun χ => by`. Use `ext`. Establish `e` using `congrArg Units.val (hz χ)`. Rewrite `e`, the goal using `[GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val]`.

Rewrite using `[← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz', Scheme.Hom.comp_appTop, CommRingCat.comp_apply]`. Use `erw [e]`. Simplify using `only [unitOn, Units.coe_map]`. Use `congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`.

Use `this.symm.trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hzz : zK = z'` using `GlobalTheory.SplitTorus.hom_ext fun χ => by`. Rewrite using `[GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.UU.chV_val, ← GlobalTheory.UU.chV_val, hzK, hcz']`. Establish `hvK' : ValAt (gγ t) (spMap b ≫ ξ) (spMap b ≫ (z ≫ j).left ≫ φ₁)`.

Use `hvK using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hzz, Over.comp_left, Over.comp_left]`. Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% (pullTorus_left hψ j), reassoc_of% hz']`. Take `⟨v, hv⟩` from `ExtNear.exists_valAt ξ (hext t)`.

Establish `hvv : spMap b ≫ v = spMap b ≫ (z ≫ j).left ≫ φ₁` using `(hv.comp (spMap b)).unique hvK'`. Establish `hveq : v = (z ≫ j).left ≫ φ₁`. Use `GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap b) hvv` and prove the remaining obligations. Rewrite using `[hv.over]`. Simplify using `only [Category.assoc, hw, Over.comp_left, Over.w_assoc]`.

Conclude with `(Category.id_comp _).symm`. Conclude with `⟨z, hz, hveq ▸ hv⟩`.
-/
theorem compat_of_compat_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (X : Type) [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (K : Type) [Field K] (b : V →+* K), Function.Injective b → ∀ (GK : Over (Sp K)) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap b) ψ), Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ ≫ φ₁) (pullTorus hψ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ X _ m c V _ _ _ ξ a G₁ _ φ₁ h₁ j hext K _ b hb GK _ ψ hψ hK
  haveI hsep : IsSeparated G.hom := hG.separated
  haveI : Flat (splitTorusAff ZU X).hom := (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
  haveI : Flat (splitTorus (Sp V) X).hom := inferInstanceAs (Flat (pullback.snd _ _))
  haveI : IsSchemeTheoreticallyDominant (spMap b) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hb
  haveI : QuasiCompact (spMap b) := inferInstance
  haveI : IsSchemeTheoreticallyDominant (bcMap (spMap b) X) :=
    IsSchemeTheoreticallyDominant.of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).flip
  have hw : φ₁ ≫ G.hom = G₁.hom ≫ ξ := h₁.1.w
  refine ⟨fun e => ?_, fun t => ?_⟩
  · have h1 := hK.1 e
    rw [← pullTorus_torusMap_comp] at h1
    simp only [Category.assoc] at h1
    have e1 := pullTorus_left hψ j
    have e2 := pullTorus_left hψ (torusMap (Sp V) (m e) ≫ j)
    refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (bcMap (spMap b) X) ?_
    · simp only [Category.assoc, Over.w, hw, Over.w_assoc, Over.comp_left]
    · calc bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ (f e).left
          = (pullTorus hψ j).left ≫ ψ ≫ φ₁ ≫ (f e).left := by rw [reassoc_of% e1]
        _ = (pullTorus hψ (torusMap (Sp V) (m e) ≫ j)).left ≫ ψ ≫ φ₁ := h1
        _ = bcMap (spMap b) X ≫ (torusMap (Sp V) (m e) ≫ j).left ≫ φ₁ := by rw [reassoc_of% e2]
  · obtain ⟨zK, hzK, hvK⟩ := hK.2 t
    haveI : NeZero L := ⟨hL.ne'⟩
    have huL : Units.map a.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
    let φh : Multiplicative X →* (Γ(Sp V, ⊤))ˣ :=
      { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
        map_one' := by simp [unitOn]
        map_mul' := fun x y => by
          simp only [toAdd_mul, map_add, unitOn]
          rw [ZMod.val_add, ← pow_eq_pow_mod _ huL, pow_add, map_mul] }
    let z : Over.mk (𝟙 (Sp V)) ⟶ splitTorus (Sp V) X := (GlobalTheory.splitTorusPointsEquiv (Sp V) X _).symm φh
    have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
      rfl
    have hwz : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
      rw [Category.assoc, Over.w z]; simp
    let z' : Over.mk (𝟙 (Sp K)) ⟶ splitTorus (Sp K) X :=
      Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hwz)
        ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
    have hz' : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
    have hcz' : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      ext
      have e := congrArg Units.val (hz χ)
      rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
      rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz',
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      erw [e]
      simp only [unitOn, Units.coe_map]
      have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      refine this.symm.trans ?_
      simp
    have hzz : zK = z' := GlobalTheory.SplitTorus.hom_ext fun χ => by
      rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.UU.chV_val,
        ← GlobalTheory.UU.chV_val, hzK, hcz']
    have hvK' : ValAt (gγ t) (spMap b ≫ ξ) (spMap b ≫ (z ≫ j).left ≫ φ₁) := by
      convert hvK using 1
      rw [hzz, Over.comp_left, Over.comp_left]
      simp only [Category.assoc]
      rw [reassoc_of% (pullTorus_left hψ j), reassoc_of% hz']
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
    have hvv : spMap b ≫ v = spMap b ≫ (z ≫ j).left ≫ φ₁ := (hv.comp (spMap b)).unique hvK'
    have hveq : v = (z ≫ j).left ≫ φ₁ := by
      refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap b) hvv
      rw [hv.over]
      simp only [Category.assoc, hw, Over.comp_left, Over.w_assoc]
      exact (Category.id_comp _).symm
    exact ⟨z, hz, hveq ▸ hv⟩

end GlobalTheory.Poinc.FibLat
