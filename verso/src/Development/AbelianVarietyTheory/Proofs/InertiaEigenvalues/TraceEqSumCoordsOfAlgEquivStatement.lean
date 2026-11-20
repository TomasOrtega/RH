import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEqSumCoordsOfAlgEquiv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTraceEqSumCoordsOfAlgEquiv.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.trace_eq_sum_of_algEquiv_pi : ∀ {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ) (e : K ≃ₐ[F] (Fin r → F)) (k : K), Algebra.trace F K k = ∑ i, e k i := by
  first | exact @GlobalTheory.trace_eq_sum_coords_of_algEquiv | exact GlobalTheory.trace_eq_sum_coords_of_algEquiv | (intros; apply GlobalTheory.trace_eq_sum_coords_of_algEquiv <;> assumption)
