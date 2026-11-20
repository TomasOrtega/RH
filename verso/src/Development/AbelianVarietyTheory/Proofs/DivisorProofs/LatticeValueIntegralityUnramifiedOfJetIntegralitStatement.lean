import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityUnramifiedOfJetIntegralit
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LatValUnr.latIntUnr | exact GlobalTheory.LatValUnr.latIntUnr | (intros; apply GlobalTheory.LatValUnr.latIntUnr <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.latticeValueIntegrality_unramified_of_jetIntegrality : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetInt → LatIntUnr := by
  first | exact @GlobalTheory.LatValUnr.latIntUnr | exact GlobalTheory.LatValUnr.latIntUnr | (intros; apply GlobalTheory.LatValUnr.latIntUnr <;> assumption)
