import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoeth
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsLocallyNoetherianOfIsQProjOverNoeth.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsQProjOver f → IsLocallyNoetherian X := by
  first | exact @GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | exact GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | (intros; apply GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth <;> assumption)
