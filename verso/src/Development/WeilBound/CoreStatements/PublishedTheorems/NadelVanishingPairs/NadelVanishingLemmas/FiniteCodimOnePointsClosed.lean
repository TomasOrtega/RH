import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCodimOnePointsClosed
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
/- English proof (citation)
Apply `GlobalTheory.Cartier.finite_coheight_one_of_ne_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteCodimOnePointsClosed.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.finite_codim_one_points_closed : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsNoetherian Y] (B : Closeds Y), B ≠ ⊤ → {v : Y | Order.coheight v = 1 ∧ v ∈ B}.Finite := by
  first | exact @_root_.GlobalTheory.Cartier.finite_coheight_one_of_ne_top | exact _root_.GlobalTheory.Cartier.finite_coheight_one_of_ne_top | (intros; apply _root_.GlobalTheory.Cartier.finite_coheight_one_of_ne_top <;> assumption)
