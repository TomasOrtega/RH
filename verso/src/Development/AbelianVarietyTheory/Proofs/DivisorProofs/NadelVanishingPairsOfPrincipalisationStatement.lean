import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingPairsOfPrincipalisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FPublishedTheorems%2FNadelVanishingPairs%2FNadelVanishingLemmas%2FNadelVanishingPairsOfPrincipalisation.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.nadel_vanishing_pairs_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair := by
  first | exact @GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | exact GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | (intros; apply GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation <;> assumption)
