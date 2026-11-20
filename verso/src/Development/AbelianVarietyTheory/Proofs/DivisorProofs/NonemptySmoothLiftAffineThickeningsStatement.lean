import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftAffineThickenings
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptySmoothLiftAffineThickenings.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.nonempty_smoothLiftAffineThickenings : ∀ D : Data, Nonempty (Lift D) := by
  first | exact @GlobalTheory.SmoothLift.LiftEx.nonempty_lift | exact GlobalTheory.SmoothLift.LiftEx.nonempty_lift | (intros; apply GlobalTheory.SmoothLift.LiftEx.nonempty_lift <;> assumption)
