import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniCoordinateStrataEtaleChartCotangent
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StrataBertini.bertini_strata_cotangent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBertiniCoordinateStrataEtaleChartCotangent.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.bertini_coordinateStrata_etaleChart_cotangent : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)), ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) → ∀ (J : Finset (Fin n)) (h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) j, h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  first | exact @GlobalTheory.StrataBertini.bertini_strata_cotangent | exact GlobalTheory.StrataBertini.bertini_strata_cotangent | (intros; apply GlobalTheory.StrataBertini.bertini_strata_cotangent <;> assumption)
