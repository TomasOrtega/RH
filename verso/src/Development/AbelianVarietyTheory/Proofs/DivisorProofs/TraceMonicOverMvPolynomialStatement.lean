import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMonicOverMvPolynomial
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.trace_monic_over_mvPolynomial` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTraceMonicOverMvPolynomial.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure : ∀ {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] {ι : Type} (z : ι → K), (∀ i, z i ∈ F) → ∀ (v : K), IsIntegral (Subring.closure (Set.range z)) v → ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧ f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by
  first | exact @GlobalTheory.trace_monic_over_mvPolynomial | exact GlobalTheory.trace_monic_over_mvPolynomial | (intros; apply GlobalTheory.trace_monic_over_mvPolynomial <;> assumption)
