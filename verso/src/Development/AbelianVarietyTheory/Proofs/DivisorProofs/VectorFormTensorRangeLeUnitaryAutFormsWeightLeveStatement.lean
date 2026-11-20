import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFormTensorRangeLeUnitaryAutFormsWeightLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVectorFormTensorRangeLeUnitaryAutFormsWeightLeve.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.vectorFormTensor_range_le_unitaryAutFormsWeightLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → LinearMap.range (Phi S lam K') ≤ forms S lam K' := by
  first | exact @GlobalTheory.BCT.TrKer.range_Phi_le_forms | exact GlobalTheory.BCT.TrKer.range_Phi_le_forms | (intros; apply GlobalTheory.BCT.TrKer.range_Phi_le_forms <;> assumption)
