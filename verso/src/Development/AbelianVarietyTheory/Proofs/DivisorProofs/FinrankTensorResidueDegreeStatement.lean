import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTensorResidueDegree
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ResidueTensorRank.finrank_tensorInl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankTensorResidueDegree.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.finrank_tensor_residue_degree : ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (T : Scheme.Pullback.Triplet f g), @Module.finrank (X.residueField T.x) T.tensor _ _ T.tensorInl.hom.toModule = g.residueDegree T.y := by
  first | exact @GlobalTheory.ResidueTensorRank.finrank_tensorInl | exact GlobalTheory.ResidueTensorRank.finrank_tensorInl | (intros; apply GlobalTheory.ResidueTensorRank.finrank_tensorInl <;> assumption)
