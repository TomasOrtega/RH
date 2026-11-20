import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O

/- English proof (translation)
Establish `h : (φ.comp (algebraMap ℚ F)).IsIntegral`. Establish `e : φ.comp (algebraMap ℚ F) = algebraMap ℚ (algebraicClosure ℚ ℂ)` using `Subsingleton.elim _ _`. Rewrite using `[e]`. Introduce `x`. Establish `hx : IsAlgebraic ℚ (x : ℂ)` using `mem_algebraicClosure_iff.1 x.2`.

Establish `hi : IsIntegral ℚ x` using `(isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val Subtype.val_injective).1 hx.isIntegral`. Conclude with `hi`. Conclude with `RingHom.IsIntegral.tower_top _ _ h`.
-/
theorem isIntegral_toAlgNumbers {F : Type} [Field F] [CharZero F]
    (φ : F →+* (algebraicClosure ℚ ℂ)) : φ.IsIntegral := by
  have h : (φ.comp (algebraMap ℚ F)).IsIntegral := by
    have e : φ.comp (algebraMap ℚ F) = algebraMap ℚ (algebraicClosure ℚ ℂ) := Subsingleton.elim _ _
    rw [e]
    intro x
    have hx : IsAlgebraic ℚ (x : ℂ) := mem_algebraicClosure_iff.1 x.2
    have hi : IsIntegral ℚ x :=
      (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val Subtype.val_injective).1 hx.isIntegral
    exact hi
  exact RingHom.IsIntegral.tower_top _ _ h

/- English proof (translation)
Take `⟨φ, hφ⟩` from `Spec.map_surjective (p ≫ Y.str)`. Establish `hint : IsIntegralHom (p ≫ Y.str)`. Rewrite using `[← hφ]`. Conclude with `IsIntegralHom.SpecMap_iff.2 (isIntegral_toAlgNumbers φ.hom)`. Establish `hp : IsIntegralHom p` using `IsIntegralHom.of_comp p Y.str`.

Establish `hc : IsClosed ({IsLocalRing.closedPoint Qb} : Set (Sp Qb))` using `IsLocalRing.isClosed_singleton_closedPoint Qb`. Use `p.isClosedMap _ hc` as an intermediate fact. Conclude with `(Set.image_singleton (f := ⇑p) (a := IsLocalRing.closedPoint Qb)) ▸ this`.
-/
theorem isClosed_below_algebraic (F : Type) [Field F] [NumberField F] (Y : Var F)
    (p : Sp Qb ⟶ Y.X) : IsClosed ({below p} : Set Y.X) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (p ≫ Y.str)
  have hint : IsIntegralHom (p ≫ Y.str) := by
    rw [← hφ]
    exact IsIntegralHom.SpecMap_iff.2 (isIntegral_toAlgNumbers φ.hom)
  have hp : IsIntegralHom p := IsIntegralHom.of_comp p Y.str
  have hc : IsClosed ({IsLocalRing.closedPoint Qb} : Set (Sp Qb)) :=
    IsLocalRing.isClosed_singleton_closedPoint Qb
  have := p.isClosedMap _ hc
  exact (Set.image_singleton (f := ⇑p) (a := IsLocalRing.closedPoint Qb)) ▸ this

end GlobalTheory.Mean4O
