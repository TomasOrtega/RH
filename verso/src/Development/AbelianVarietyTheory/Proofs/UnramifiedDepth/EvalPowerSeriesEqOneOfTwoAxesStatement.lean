import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvalPowerSeriesEqOneOfTwoAxes
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FEvalPowerSeriesEqOneOfTwoAxes.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.evalPowerSeries_eq_one_of_two_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ a a' b : Fin d → A, (∀ j, a j ∈ Ideal.span {e}) → (∀ j, a' j ∈ Ideal.span {e}) → (∀ j, IsNilpotent (b j)) → evP ![a, a', b] ph = 1 := by
  first | exact @GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | exact GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | (intros; apply GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes <;> assumption)
