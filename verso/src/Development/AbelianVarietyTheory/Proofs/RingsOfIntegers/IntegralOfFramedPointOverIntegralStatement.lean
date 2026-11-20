import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfFramedPointOverIntegral
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FRingsOfIntegers%2FIntegralOfFramedPointOverIntegral.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.integral_of_framed_point_over_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (T : CDVR) (io : c.F →+* T.Fr) (io₂ : d.c₂.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; letI := io₂.toAlgebra; (∀ a : c.F, io₂ (d.eF a) = io a) → ∀ y₂ : FrPt d.Xo₂ d.c₂ T.Fr, FrOver d y₂ y.1 → Integral T io₂ y₂ := by
  first | exact @GlobalTheory.PlaceInt.integral_of_frOver | exact GlobalTheory.PlaceInt.integral_of_frOver | (intros; apply GlobalTheory.PlaceInt.integral_of_frOver <;> assumption)
