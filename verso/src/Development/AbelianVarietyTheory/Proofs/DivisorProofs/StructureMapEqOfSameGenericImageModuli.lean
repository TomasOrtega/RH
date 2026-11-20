import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

/- English proof (translation)
Introduce `o R V _ _ _ _ _ X sX y b hy θ₁ θ₂ κ₁ κ₂ h₁ h₂ hκ`. Establish `key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ → jK V ≫ spMap (θ.comp b) = κ ≫ y ≫ sX`. Introduce `θ κ h`. Rewrite using `[hy, ← Category.assoc, h, Category.assoc]`. Simplify using `only [jK, spMap, ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `e : jK V ≫ spMap (θ₁.comp b) = jK V ≫ spMap (θ₂.comp b)`. Rewrite using `[key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hκ, Category.assoc]`. Simplify using `only [jK, spMap, ← Spec.map_comp] at e`. Establish `e2` using `congrArg CommRingCat.Hom.hom (Spec.map_injective e)`.

Use extensionality with `r`. Use `congrArg (fun f => f r) e2` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this`. Conclude with `IsFractionRing.injective V (FractionRing V) this`.
-/
theorem GlobalTheory.TInj.baseEq_of_sameImage : ∀ {o R V : Type} [CommRing o] [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {X : Scheme.{0}} (sX : X ⟶ Sp o) (y : Sp (FractionRing R) ⟶ X) (b : o →+* R), y ≫ sX = jK R ≫ spMap b → ∀ (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → θ₁.comp b = θ₂.comp b := by
  intro o R V _ _ _ _ _ X sX y b hy θ₁ θ₂ κ₁ κ₂ h₁ h₂ hκ
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp b) = κ ≫ y ≫ sX := by
    intro θ κ h
    rw [hy, ← Category.assoc, h, Category.assoc]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl
  have e : jK V ≫ spMap (θ₁.comp b) = jK V ≫ spMap (θ₂.comp b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hκ, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this
