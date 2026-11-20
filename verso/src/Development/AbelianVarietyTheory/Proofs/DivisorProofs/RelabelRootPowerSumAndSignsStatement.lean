import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelabelRootPowerSumAndSigns
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootIdx
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR
open GlobalTheory.BcEigen
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelabelRootPowerSumAndSigns.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.relabel_root_power_sum_and_signs : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ), j ≤ N →
    rename (rootIdx ι N j) (∑ τ, pSum τ 2 : Pol ι N) = sq2 (rkB ι N j) ∧
    rename (rootIdx ι N j) (lamA ι N j) = linE (rkB ι N j) lamSign ∧
    ∀ al be : ℝ, rename (rootIdx ι N j) (invForm j (fun _ : ι => al) (fun _ => be) : Pol ι N) =
      ∑ a, C (cond a.2 al be) * eSum (rkB ι N j) a := by
  first | exact @GlobalTheory.BcEigen.relabel_sums | exact GlobalTheory.BcEigen.relabel_sums | (intros; apply GlobalTheory.BcEigen.relabel_sums <;> assumption)
