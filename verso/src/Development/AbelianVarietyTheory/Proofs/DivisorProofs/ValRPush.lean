import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.DZero

/- English proof (translation)
Establish `h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U` using `fun p _ => h (Set.mem_univ _)`. Rewrite using `[valR, valR, dif_pos h, dif_pos h']`. Establish `e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Conclude with `(Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm`.

Establish `e2` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)`. Rewrite using `[e1]`. Conclude with `congrArg (fun k => k.hom ((x.appLE U ⊤ h).hom f)) e2`.
-/
theorem valR_push {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ => h (Set.mem_univ _)
  rw [valR, valR, dif_pos h, dif_pos h']
  have e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  rw [e1]
  exact congrArg (fun k => k.hom ((x.appLE U ⊤ h).hom f)) e2

/- English proof (translation)
Introduce `R _ _ _ _ D _ _ _ N ν g d U f hU`. Establish `h0 : d.ex 0 = 1`. Use `d.ex_add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`.

Establish `e : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R` using `R) ℂ) (DegPre.zeroT D (TE R ℂ))).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by`. Establish `: lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R` using `R) ℂ) (DegPre.zeroT D (TE R ℂ)) = (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by`. Rewrite using `[comp_lift, Category.comp_id, h0, map_one, Hom.one_def, ← Category.assoc, comp_toUnit]`. Rewrite using `[this, Over.comp_left]`. Both sides reduce to the same expression.

Rewrite using `[e, valR_push _ _ _ hU, map_zero, TrivSqZeroExt.inr_zero, add_zero]`. Both sides reduce to the same expression.
-/
theorem isD_zero : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), IsD ν d 0 (DegPre.zeroT D (TE R ℂ)) := by
  intro R _ _ _ _ D _ _ _ N ν g d U f hU
  have h0 : d.ex 0 = 1 := by
    have := d.ex_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have e : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
      (DegPre.zeroT D (TE R ℂ))).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by
    have : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
        (DegPre.zeroT D (TE R ℂ)) =
        (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫
          lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by
      rw [comp_lift, Category.comp_id, h0, map_one, Hom.one_def, ← Category.assoc, comp_toUnit]
    rw [this, Over.comp_left]
    rfl
  rw [e, valR_push _ _ _ hU, map_zero, TrivSqZeroExt.inr_zero, add_zero]
  rfl

end GlobalTheory.MBLow.Cl.DZero

end
