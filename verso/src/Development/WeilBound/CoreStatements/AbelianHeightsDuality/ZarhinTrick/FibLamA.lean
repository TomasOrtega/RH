import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsLBZb

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

instance isMonHom_prj (G : Over S) [GrpObj G] (i : Fin 4) : IsMonHom (prj G i) := by
  fin_cases i <;> dsimp [prj] <;> infer_instance

section Base

variable {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify by unfolding definitions.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem toBase_injective (G : Over S) {T : Over (Sp Ω)} {x y : T ⟶ (Over.pullback s).obj G}
    (h : toBase G s x = toBase G s y) : x = y := by
  have hl := congrArg CommaMorphism.left h
  have hx := Over.w x
  have hy := Over.w y
  ext1
  apply pullback.hom_ext
  · exact hl
  · dsimp at hx hy
    rw [hx, hy]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem toBase_mul (G : Over S) [GrpObj G] {T : Over (Sp Ω)} (x y : T ⟶ (Over.pullback s).obj G) :
    toBase G s (x * y) = toBase G s x * toBase G s y := GlobalTheory.UU.toBase_mul_pullback G s T x y

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem toBase_one (G : Over S) [GrpObj G] {T : Over (Sp Ω)} :
    toBase G s (1 : T ⟶ (Over.pullback s).obj G) = 1 := by
  have h := toBase_mul s G (1 : T ⟶ (Over.pullback s).obj G) 1
  rw [_root_.mul_one] at h
  simpa using h

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem toBase_inv (G : Over S) [GrpObj G] {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj G) :
    toBase G s x⁻¹ = (toBase G s x)⁻¹ := by
  have h := toBase_mul s G x⁻¹ x
  rw [inv_mul_cancel, toBase_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem toBase_map {G G' : Over S} (f : G ⟶ G') {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj G) :
    toBase G' s (x ≫ (Over.pullback s).map f) = toBase G s x ≫ f := by
  ext
  simp [toBase, Over.pullback, pullback.lift_fst]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.
-/
theorem toBase_comp (G : Over S) {T T' : Over (Sp Ω)} (v : T' ⟶ T) (x : T ⟶ (Over.pullback s).obj G) :
    toBase G s (v ≫ x) = (Over.homMk v.left (by dsimp; rw [← Category.assoc, Over.w v]) : Over.mk (T'.hom ≫ s) ⟶ Over.mk (T.hom ≫ s)) ≫
      toBase G s x := by
  apply Over.OverMorphism.ext
  simp [toBase]

end Base

end PositivityTheory.PrwZar
