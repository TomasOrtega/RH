import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | exact GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | (intros; apply GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  first | exact @GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | exact GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | (intros; apply GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main <;> assumption)
