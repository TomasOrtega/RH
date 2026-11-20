import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.RingPoint

/- English proof (translation)
Establish `h : (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop = (Scheme.ΓSpecIso (CommRingCat.of D)).hom ≫ CommRingCat.ofHom θ`. Rewrite using `[Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]`. Conclude with `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ : CommRingCat.of D ⟶ Γ(Z, ⊤))`. Conclude with `congrArg (fun q => q.hom a) h`.
-/
theorem toSpec_appTop {Z : Scheme.{0}} {D : Type} [CommRing D] (θ : D →+* Γ(Z, ⊤)) (a : Γ(Spec (CommRingCat.of D), ⊤)) :
    (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop.hom a = θ ((Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom a) := by
  have h : (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of D)).hom ≫ CommRingCat.ofHom θ := by
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ : CommRingCat.of D ⟶ Γ(Z, ⊤))
  exact congrArg (fun q => q.hom a) h

/- English proof (translation)
Set `p : Spec (CommRingCat.of D) ⟶ Y.left` to `Spec.map (CommRingCat.ofHom κ : Γ(Y.left, ⊤) ⟶ CommRingCat.of D) ≫ Y.left.isoSpec.inv`. Establish `hp : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (p.appTop.hom b) = κ b` using `fun b => by`. Establish `h : p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom = CommRingCat.ofHom κ`. Rewrite using `[Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]`. Simplify using the standard rewrite rules.

Conclude with `congrArg (fun q => q.hom b) h`. Use `⟨Over.mk (p ≫ Y.hom), Over.homMk p rfl, (Scheme.ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv, inferInstanceAs (IsAffine (Spec _)), hp, fun Z y θ hθ => ?_⟩` and prove the remaining obligations. Establish `h : (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ≫ p = y.left`. Use `ext_of_isAffine ?_` and prove the remaining obligations. Use extensionality with `b`.

Rewrite using `[Scheme.Hom.comp_appTop]`. Conclude with `(toSpec_appTop θ _).trans ((congrArg θ (hp b)).trans (hθ b))`. Use `⟨Over.homMk (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ?_, Over.OverMorphism.ext h, toSpec_appTop θ⟩` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.hom) h).trans (Over.w y))`.
-/
theorem exists_ringPoint {S : Scheme.{0}} (Y : Over S) [IsAffine Y.left] (D : Type) [CommRing D]
    (κ : Γ(Y.left, ⊤) →+* D) : ∃ (U : Over S) (y₀ : U ⟶ Y) (e : Γ(U.left, ⊤) ≃+* D), IsAffine U.left ∧
      (∀ b, e (y₀.left.appTop.hom b) = κ b) ∧
      ∀ (Z : Over S) (y : Z ⟶ Y) (θ : D →+* Γ(Z.left, ⊤)), (∀ b, θ (κ b) = y.left.appTop.hom b) →
        ∃ σ : Z ⟶ U, σ ≫ y₀ = y ∧ ∀ a, σ.left.appTop.hom a = θ (e a) := by
  let p : Spec (CommRingCat.of D) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom κ : Γ(Y.left, ⊤) ⟶ CommRingCat.of D) ≫ Y.left.isoSpec.inv
  have hp : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (p.appTop.hom b) = κ b := fun b => by
    have h : p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom = CommRingCat.ofHom κ := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      simp
    exact congrArg (fun q => q.hom b) h
  refine ⟨Over.mk (p ≫ Y.hom), Over.homMk p rfl, (Scheme.ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv,
    inferInstanceAs (IsAffine (Spec _)), hp, fun Z y θ hθ => ?_⟩
  have h : (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ≫ p = y.left := by
    refine ext_of_isAffine ?_
    ext b
    rw [Scheme.Hom.comp_appTop]
    exact (toSpec_appTop θ _).trans ((congrArg θ (hp b)).trans (hθ b))
  refine ⟨Over.homMk (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ?_, Over.OverMorphism.ext h, toSpec_appTop θ⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.hom) h).trans (Over.w y))

def strMap {A : Type} [CommRing A] (Z : Over (Spec (CommRingCat.of A))) : A →+* Γ(Z.left, ⊤) :=
  Z.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/- English proof (translation)
Rewrite using `[strMap, strMap, ← Over.w y, Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.
-/
theorem appTop_strMap {A : Type} [CommRing A] {Z Y : Over (Spec (CommRingCat.of A))} (y : Z ⟶ Y) (a : A) :
    y.left.appTop.hom (strMap Y a) = strMap Z a := by
  rw [strMap, strMap, ← Over.w y, Scheme.Hom.comp_appTop]; rfl

/- English proof (translation)
Establish `nat : ∀ a, (red J).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv.hom (Ideal.Quotient.mk J a)` using `fun a => congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J) : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J))).symm`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs⟩ a ha`. Rewrite using `[strMap, ← hs, Scheme.Hom.comp_appTop]`. Express the relevant statement in the definitionally equal form `s.appTop.hom ((red J).appTop.hom _) = 0`.

Rewrite using `[nat, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]`. Introduce `h`. Use `⟨Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (strMap Z) h)), ext_of_isAffine ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv]`. Use extensionality with `a`.

Rewrite using `[Scheme.Hom.comp_appTop]`. Use `(congrArg _ (nat a)).trans ((toSpec_appTop _ _).trans ?_)` and prove the remaining obligations. Rewrite using `[← CommRingCat.comp_apply, Iso.inv_hom_id]`. Both sides reduce to the same expression.
-/
theorem exists_comp_red_iff {A : Type} [CommRing A] (J : Ideal A) (Z : Over (Spec (CommRingCat.of A))) :
    (∃ s, s ≫ red J = Z.hom) ↔ ∀ a ∈ J, strMap Z a = 0 := by
  have nat : ∀ a, (red J).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv.hom (Ideal.Quotient.mk J a) := fun a =>
    congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk J) : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J))).symm
  constructor
  · rintro ⟨s, hs⟩ a ha
    rw [strMap, ← hs, Scheme.Hom.comp_appTop]
    change s.appTop.hom ((red J).appTop.hom _) = 0
    rw [nat, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]
  · intro h
    refine ⟨Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (strMap Z) h)), ext_of_isAffine ?_⟩
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv]
    ext a
    rw [Scheme.Hom.comp_appTop]
    refine (congrArg _ (nat a)).trans ((toSpec_appTop _ _).trans ?_)
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl

end GlobalTheory.UU.RingPoint
end
