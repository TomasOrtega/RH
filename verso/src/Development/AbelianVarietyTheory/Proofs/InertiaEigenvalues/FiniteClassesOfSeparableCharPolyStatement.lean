import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesOfSeparableCharPoly
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteClassesOfSeparableCharPoly.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.finite_classes_of_separable_charPoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Finite B.Cl := by
  first | exact @GlobalTheory.UnitLemma.ClFin.finite_Cl_of_separable | exact GlobalTheory.UnitLemma.ClFin.finite_Cl_of_separable | (intros; apply GlobalTheory.UnitLemma.ClFin.finite_Cl_of_separable <;> assumption)
