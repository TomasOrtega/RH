import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormComplexEmbeddingEntryDefiniteUnitaryRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormComplexEmbeddingEntryDefiniteUnitaryRational.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.norm_complexEmbedding_entry_definiteUnitaryRational_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ (γ.1.val i j)‖ ≤ 1 := by
  first | exact @GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one | exact GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one | (intros; apply GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one <;> assumption)
