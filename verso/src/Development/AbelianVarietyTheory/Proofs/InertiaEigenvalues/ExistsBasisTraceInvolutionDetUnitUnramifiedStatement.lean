import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisTraceInvolutionDetUnitUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsBasisTraceInvolutionDetUnitUnramified.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧ val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0 := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit | exact GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit | (intros; apply GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit <;> assumption)
