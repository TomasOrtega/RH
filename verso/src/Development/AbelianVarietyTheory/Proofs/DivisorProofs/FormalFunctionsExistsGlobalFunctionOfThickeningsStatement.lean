import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFunctionsExistsGlobalFunctionOfThickenings
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormalFunctions.exists_of_thick` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalFunctionsExistsGlobalFunctionOfThickenings.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.formalFunctions_exists_globalFunction_of_thickenings : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ (X : Over (Sp A)), IsProper X.hom → ∀ f : ∀ e : ℕ, Γ((thickObj A I e X).left, ⊤), (∀ e, (thickMap A I e X).appTop.hom (f (e + 1)) = f e) → ∃ s : Γ(X.left, ⊤), ∀ e, (pullback.fst X.hom (thick A I e)).appTop.hom s = f e := by
  first | exact @GlobalTheory.FormalFunctions.exists_of_thick | exact GlobalTheory.FormalFunctions.exists_of_thick | (intros; apply GlobalTheory.FormalFunctions.exists_of_thick <;> assumption)
