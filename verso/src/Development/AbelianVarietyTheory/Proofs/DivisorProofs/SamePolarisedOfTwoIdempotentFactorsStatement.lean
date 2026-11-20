import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedOfTwoIdempotentFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.TwoFac.samePol_of_two_factors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSamePolarisedOfTwoIdempotentFactors.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.samePolarised_of_two_idempotentFactors : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ D' : DegPre R), D₁.TauBimult → ∀ (F₁ : Factor D₁ D') (F₂ : Factor D₂ D'), F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e → F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f → (∀ z : D'.X, F₁.e • z = F₂.e • z) → (∀ z : D'.X, F₁.f • z = F₂.f • z) → SamePol D₁ D₂ := by
  first | exact @GlobalTheory.Mum.TwoFac.samePol_of_two_factors | exact GlobalTheory.Mum.TwoFac.samePol_of_two_factors | (intros; apply GlobalTheory.Mum.TwoFac.samePol_of_two_factors <;> assumption)
