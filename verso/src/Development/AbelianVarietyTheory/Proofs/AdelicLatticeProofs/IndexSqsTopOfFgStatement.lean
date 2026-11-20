import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSqsTopOfFg
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FIndexSqsTopOfFg.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.index_sqs_of_fg : ∀ (G : Type) [CommGroup G] [Group.FG G], (sqs (⊤ : Subgroup G)).index = 2 ^ Module.finrank ℤ (Additive G) * Nat.card {a : G // a ^ 2 = 1} := by
  first | exact @GlobalTheory.QNorm.index_sqs_top_of_fg | exact GlobalTheory.QNorm.index_sqs_top_of_fg | (intros; apply GlobalTheory.QNorm.index_sqs_top_of_fg <;> assumption)
