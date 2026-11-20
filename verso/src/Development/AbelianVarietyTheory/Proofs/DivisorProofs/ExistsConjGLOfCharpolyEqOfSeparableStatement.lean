import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsConjGLOfCharpolyEqOfSeparable.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_conj_GL_of_charpoly_eq_of_separable : ∀ (K : Type) [Field K] (n : ℕ) (a b : GL (Fin n) K), a.val.charpoly = b.val.charpoly → a.val.charpoly.Separable → ∃ h : GL (Fin n) K, b = h⁻¹ * a * h := by
  first | exact @GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable | exact GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable | (intros; apply GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable <;> assumption)
