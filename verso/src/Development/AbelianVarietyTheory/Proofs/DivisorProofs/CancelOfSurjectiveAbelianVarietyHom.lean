import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompactStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A B p hp C f g h`. Establish `hB : IsIntegral B.X.left` using `(GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B).1`. Establish `hsep : IsSeparated C.X.hom` using `C.ab.proper.toIsSeparated`. Apply `hom_ext` to reduce the goal to its premises. Use `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated C.X.hom ((Over.w f.hom).trans (Over.w g.hom).symm) p.hom.left ?_)` and prove the remaining obligations.

Use `congrArg (fun u => (Hom.hom u).left) h` as an intermediate fact. Simplify `this` using `only [comp_hom, Over.comp_left]`.
-/
theorem cancel_of_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left →
    ∀ (C : AbVar K) (f g : B ⟶ C), p ≫ f = p ≫ g → f = g := by
  intro K _ A B p hp C f g h
  have hB : IsIntegral B.X.left := (GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B).1
  have hsep : IsSeparated C.X.hom := C.ab.proper.toIsSeparated
  apply hom_ext
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated C.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) p.hom.left ?_)
  have := congrArg (fun u => (Hom.hom u).left) h
  simpa only [comp_hom, Over.comp_left] using this

end GlobalTheory.AV.AbVar
