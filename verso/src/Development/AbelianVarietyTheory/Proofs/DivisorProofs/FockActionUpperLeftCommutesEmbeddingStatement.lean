import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionUpperLeftCommutesEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CharPair.FirstBlock.act_first_block` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFockActionUpperLeftCommutesEmbedding.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.fock_action_upper_left_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a a' : Fin P) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inl a') G) := by
  first | exact @GlobalTheory.CharPair.FirstBlock.act_first_block | exact GlobalTheory.CharPair.FirstBlock.act_first_block | (intros; apply GlobalTheory.CharPair.FirstBlock.act_first_block <;> assumption)
