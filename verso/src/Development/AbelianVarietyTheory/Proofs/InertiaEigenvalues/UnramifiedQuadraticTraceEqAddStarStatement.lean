import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticTraceEqAddStar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.trace_eq_add_star` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnramifiedQuadraticTraceEqAddStar.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.unramifiedQuadratic_trace_eq_add_star : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y := by
  first | exact @GlobalTheory.trace_eq_add_star | exact GlobalTheory.trace_eq_add_star | (intros; apply GlobalTheory.trace_eq_add_star <;> assumption)
