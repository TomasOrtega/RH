import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEvalFormModRelationEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralEvalFormModRelationEq.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.integral_evalForm_mod_relation_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (A : HermLB p) (σ : k →+* ℂ)
    (Z Z' : MvPolynomial (Fin 4) ℝ), (MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2 : MvPolynomial (Fin 4) ℝ) ∣ Z - Z' →
      (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z) = (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z') := by
  first | exact @GlobalTheory.FlagChernWeil.integral_evalForm_flag_family_eq | exact GlobalTheory.FlagChernWeil.integral_evalForm_flag_family_eq | (intros; apply GlobalTheory.FlagChernWeil.integral_evalForm_flag_family_eq <;> assumption)
