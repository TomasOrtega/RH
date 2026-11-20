import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralDelDbarZero.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.integral_del_dbar_zero : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  first | exact @GlobalTheory.CxFormStokesBoth.stokes | exact GlobalTheory.CxFormStokesBoth.stokes | (intros; apply GlobalTheory.CxFormStokesBoth.stokes <;> assumption)
