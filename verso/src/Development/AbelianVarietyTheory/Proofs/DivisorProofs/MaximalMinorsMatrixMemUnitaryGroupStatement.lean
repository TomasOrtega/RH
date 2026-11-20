import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalMinorsMatrixMemUnitaryGroup
import Mathlib

open Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMaximalMinorsMatrixMemUnitaryGroup.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ), M ∈ Matrix.unitaryGroup (Fin N) ℂ → (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} => (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈ Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  first | exact @GlobalTheory.minorsMatrix_mem_unitaryGroup | exact GlobalTheory.minorsMatrix_mem_unitaryGroup | (intros; apply GlobalTheory.minorsMatrix_mem_unitaryGroup <;> assumption)
