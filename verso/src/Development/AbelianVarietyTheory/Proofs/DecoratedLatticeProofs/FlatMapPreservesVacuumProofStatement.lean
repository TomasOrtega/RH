import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.FlatVacuum.flatVac` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFlatMapPreservesVacuumProof.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.flatMapPreservesVacuum_proof : ∀ D : D7, GlobalTheory.FinPl.FlatVac D := by
  first | exact @GlobalTheory.FinPl.FlatVacuum.flatVac | exact GlobalTheory.FinPl.FlatVacuum.flatVac | (intros; apply GlobalTheory.FinPl.FlatVacuum.flatVac <;> assumption)
