import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorExistsUniqueSubMatrixFrobeniusEq
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWittVectorExistsUniqueSubMatrixFrobeniusEq.lean&line=196#L196)
-/
theorem _root_.GlobalTheory.T.wittVector_existsUnique_sub_matrix_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)), (∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) → ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by
  first | exact @GlobalTheory.wittSolve_unique | exact GlobalTheory.wittSolve_unique | (intros; apply GlobalTheory.wittSolve_unique <;> assumption)
