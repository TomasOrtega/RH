import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTraceDualWeylModuleInvRationalPointEqConjCharAt.lean&line=199#L199)
-/
theorem _root_.GlobalTheory.T.trace_dualWeylModule_inv_rationalPoint_eq_conj_charAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : DomWeight n) (γ : UE E n) (v : InfinitePlace E), LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map v.embedding (γ⁻¹).1)) = starRingEnd ℂ (chAt lam (γ.1.val.charpoly.map v.embedding)) := by
  first | exact @GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt | exact GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt | (intros; apply GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt <;> assumption)
