import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramDetEqNormMulGramDetOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGramDetEqNormMulGramDetOne.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.gramDet_eq_norm_mul_gramDet_one : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul | exact GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul | (intros; apply GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul <;> assumption)
