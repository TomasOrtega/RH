import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryConjIffExistsCentralizerNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUnitaryConjIffExistsCentralizerNorm.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_unitary_conj_iff_exists_centralizer_norm : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ h : GL (Fin n) K), (∃ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) K), h⁻¹ * γ * h = g⁻¹ * γ * g) ↔ ∃ c : Matrix (Fin n) (Fin n) K, c * γ.val = γ.val * c ∧ cT σ c * c = (h.val * cT σ h.val)⁻¹ := by
  first | exact @GlobalTheory.UnitaryConj.main | exact GlobalTheory.UnitaryConj.main | (intros; apply GlobalTheory.UnitaryConj.main <;> assumption)
