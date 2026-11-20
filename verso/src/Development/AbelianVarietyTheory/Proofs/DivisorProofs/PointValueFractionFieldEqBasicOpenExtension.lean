import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecAppLETopEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

/- English proof (translation)
Introduce `R _ G Ω _ _ φ x' hx c iota hiota O h hO θ`. Rewrite using `[GlobalTheory.CechKSSmul.valR_appLE_comp _ G.hom (GlobalTheory.HeatV.bo R c).1 O h hO θ]`. Establish `hz : (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom = Spec.map (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ))`. Rewrite using `[Category.assoc, hx]`. Use `show Spec.map _ ≫ Spec.map _ = _`.

Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `h' : ⊤ ≤ ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom) ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1` using `fun p hp => h (hO hp)`. Use `set s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c with hs`. Use `set z := (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom with hzdef`.

Set `F : Γ(Sp R, (Sp R).basicOpen s) →+* FractionRing Ω` to `(Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom`. Establish `hF : ∀ θ, valR z (GlobalTheory.HeatV.bo R c).1 θ = F θ` using `fun θ => by`. Simplify using `only [valR, dif_pos h']`. Both sides reduce to the same expression. It suffices to establish `e : F = iota by rw [hF]; exact DFunLike.congr_fun e θ`.

Use `IsLocalization.ringHom_ext (Submonoid.powers s) (S := Γ(Sp R, (Sp R).basicOpen s)) ?_` and prove the remaining obligations. Use extensionality with `y0`. Take `⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r = y0` from `⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y0, by simp⟩`. Establish `e1 : algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = GlobalTheory.HeatV.resV R c r` using `rfl`. Express the relevant statement in the definitionally equal form `F (GlobalTheory.HeatV.resV R c r) = iota (GlobalTheory.HeatV.resV R c r)`.

Rewrite using `[hiota]`. Use `show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom ((z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom (GlobalTheory.HeatV.resV R c r)) = _`. Establish `e2 : (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U` using `⊤) s)).op ≫ z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h' = z.appTop := by`. Conclude with `(Scheme.Hom.map_appLE z h' _).trans (Scheme.Hom.appLE_eq_app z)`. Establish `e3 : (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U` using `⊤) s)).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = z.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by`.

Rewrite using `[← e2]`. Both sides reduce to the same expression. Rewrite using `[show (GlobalTheory.HeatV.resV R c r) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) from rfl, e3]`. Rewrite using `[hz]`. Establish `n` using `congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)))`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n`. Rewrite using `[n]`. Simplify using the standard rewrite rules.
-/
theorem valR_cst_eq_iota : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R) (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* FractionRing Ω), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = algebraMap Ω (FractionRing Ω) (φ r)) → ∀ (O : G.left.Opens) (h : O ≤ G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ O → ∀ θ, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') O (GlobalTheory.HeatV.cst G.hom _ h θ) = iota θ := by
  intro R _ G Ω _ _ φ x' hx c iota hiota O h hO θ
  rw [GlobalTheory.CechKSSmul.valR_appLE_comp _ G.hom (GlobalTheory.HeatV.bo R c).1 O h hO θ]
  have hz : (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)) := by
    rw [Category.assoc, hx]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have h' : ⊤ ≤ ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom) ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 :=
    fun p hp => h (hO hp)
  set s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c with hs
  set z := (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom with hzdef
  let F : Γ(Sp R, (Sp R).basicOpen s) →+* FractionRing Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
  have hF : ∀ θ, valR z (GlobalTheory.HeatV.bo R c).1 θ = F θ := fun θ => by
    simp only [valR, dif_pos h']; rfl
  suffices e : F = iota by rw [hF]; exact DFunLike.congr_fun e θ
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (S := Γ(Sp R, (Sp R).basicOpen s)) ?_
  ext y0
  obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r = y0 :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y0, by simp⟩
  have e1 : algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      GlobalTheory.HeatV.resV R c r := rfl
  change F (GlobalTheory.HeatV.resV R c r) = iota (GlobalTheory.HeatV.resV R c r)
  rw [hiota]
  show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom
    ((z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom (GlobalTheory.HeatV.resV R c r)) = _
  have e2 : (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op ≫ z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h' =
      z.appTop := by
    exact (Scheme.Hom.map_appLE z h' _).trans (Scheme.Hom.appLE_eq_app z)
  have e3 : (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
      (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      z.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← e2]; rfl
  rw [show (GlobalTheory.HeatV.resV R c r) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) from rfl, e3]
  rw [hz]
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [n]
  simp

end GlobalTheory.HeatV
