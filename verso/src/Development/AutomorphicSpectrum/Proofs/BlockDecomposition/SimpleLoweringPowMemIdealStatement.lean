import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleLoweringPowMemIdeal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent | exact GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent | (intros; apply GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.simple_lowering_pow_mem_ideal : ∀ {n : ℕ} (i j : Fin n) (x : U n), (j : ℕ) = i + 1 → ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent | exact GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent | (intros; apply GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent <;> assumption)
