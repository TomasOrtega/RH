import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFunctionFieldModelHomOfProjective
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ProjModelSurj.surjective_of_isProjOver` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSurjectiveFunctionFieldModelHomOfProjective.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.surjective_functionFieldModelHom_of_projective : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (X M : RatModel o Ω) (f : M.Z ⟶ X.Z),
    X.IsHom M (AlgHom.id o Ω) f → IsProjOver M.s → Function.Surjective f := by
  first | exact @GlobalTheory.ProjModelSurj.surjective_of_isProjOver | exact GlobalTheory.ProjModelSurj.surjective_of_isProjOver | (intros; apply GlobalTheory.ProjModelSurj.surjective_of_isProjOver <;> assumption)
