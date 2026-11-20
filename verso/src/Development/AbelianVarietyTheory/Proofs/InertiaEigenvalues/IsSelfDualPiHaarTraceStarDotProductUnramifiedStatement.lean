import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSelfDualPiHaarTraceStarDotProductUnramified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsSelfDualPiHaarTraceStarDotProductUnramified.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → @SelfDual (Fin r → E) _ _ (@MeasurableSpace.pi (Fin r) (fun _ => E) (fun _ => M.mE)) (@Measure.pi (Fin r) (fun _ => E) _ (fun _ => M.mE) (fun _ => M.μE)) (fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))) := by
  first | exact @GlobalTheory.JR.selfDual_pi_trace | exact GlobalTheory.JR.selfDual_pi_trace | (intros; apply GlobalTheory.JR.selfDual_pi_trace <;> assumption)
