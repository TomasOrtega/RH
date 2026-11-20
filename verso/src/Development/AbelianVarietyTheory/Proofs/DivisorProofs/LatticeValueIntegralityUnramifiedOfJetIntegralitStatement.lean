import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityUnramifiedOfJetIntegralit
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatValUnr.latIntUnr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeValueIntegralityUnramifiedOfJetIntegralit.lean&line=232#L232)
-/
theorem _root_.GlobalTheory.T.latticeValueIntegrality_unramified_of_jetIntegrality : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetInt → LatIntUnr := by
  first | exact @GlobalTheory.LatValUnr.latIntUnr | exact GlobalTheory.LatValUnr.latIntUnr | (intros; apply GlobalTheory.LatValUnr.latIntUnr <;> assumption)
