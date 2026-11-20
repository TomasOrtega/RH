import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosed
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFirstChernRealClosed.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.firstChern_real_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L : HermLB p, (hX.atlas σ).IsRealForm 1 (fld _ (c1F hX σ L)) ∧ (hX.atlas σ).del (fld _ (c1F hX σ L)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c1F hX σ L)) = 0 := by
  first | exact @GlobalTheory.LineForm.FirstChern.c1F_isRealForm_closed | exact GlobalTheory.LineForm.FirstChern.c1F_isRealForm_closed | (intros; apply GlobalTheory.LineForm.FirstChern.c1F_isRealForm_closed <;> assumption)
