import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTracePowAddMulUnitNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDetTracePowAddMulUnitNeZero.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.det_trace_pow_add_mul_unit_ne_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u → (Matrix.of fun k l : Fin (Module.finrank K.E B.A) => Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | exact GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | (intros; apply GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero <;> assumption)
