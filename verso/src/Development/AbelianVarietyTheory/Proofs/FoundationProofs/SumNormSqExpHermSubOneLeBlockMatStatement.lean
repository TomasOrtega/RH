import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumNormSqExpHermSubOneLeBlockMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CartanLip.exp_mul_exp_sub_one_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSumNormSqExpHermSubOneLeBlockMat.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.sum_norm_sq_exp_herm_sub_one_le_blockMat : ∀ (p q : ℕ) (H H' : Mat p q), Hᴴ = H → H'ᴴ = H' → ∑ a, ∑ b, ‖(NormedSpace.exp (-(Complex.I • H')) * NormedSpace.exp (Complex.I • H) - 1) a b‖ ^ 2 ≤ ∑ a, ∑ b, ‖(H - H') a b‖ ^ 2 := by
  first | exact @GlobalTheory.CartanLip.exp_mul_exp_sub_one_le | exact GlobalTheory.CartanLip.exp_mul_exp_sub_one_le | (intros; apply GlobalTheory.CartanLip.exp_mul_exp_sub_one_le <;> assumption)
