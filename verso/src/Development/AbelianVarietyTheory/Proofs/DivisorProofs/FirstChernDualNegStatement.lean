import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernDualNeg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LineForm.c1F_dual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFirstChernDualNeg.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.firstChern_dual_neg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L : HermLB p, c1F hX σ L.dual = -c1F hX σ L := by
  first | exact @GlobalTheory.LineForm.c1F_dual | exact GlobalTheory.LineForm.c1F_dual | (intros; apply GlobalTheory.LineForm.c1F_dual <;> assumption)
