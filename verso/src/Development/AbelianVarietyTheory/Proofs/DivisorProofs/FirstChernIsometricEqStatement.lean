import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LineForm.c1F_eq_of_isometric` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFirstChernIsometricEq.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.firstChern_isometric_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L M : HermLB p, L.Isometric M → c1F hX σ L = c1F hX σ M := by
  first | exact @GlobalTheory.LineForm.c1F_eq_of_isometric | exact GlobalTheory.LineForm.c1F_eq_of_isometric | (intros; apply GlobalTheory.LineForm.c1F_eq_of_isometric <;> assumption)
