import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeValueIntegralityRamifiedOfExpansion.lean&line=166#L166)
-/
theorem _root_.GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → Expansion → LatIntRam := by
  first | exact @GlobalTheory.LatValRam.latIntRam | exact GlobalTheory.LatValRam.latIntRam | (intros; apply GlobalTheory.LatValRam.latIntRam <;> assumption)
