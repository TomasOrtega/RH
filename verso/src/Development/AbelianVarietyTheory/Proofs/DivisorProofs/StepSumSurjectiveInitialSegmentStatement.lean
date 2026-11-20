import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepSumSurjectiveInitialSegment
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.stepSum_surj_of_initial` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStepSumSurjectiveInitialSegment.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.step_sum_surjective_initial_segment : ∀ {r : ℕ} {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) → ∀ (v : Fin r → ℝ), (∀ i ∉ S, v i = 0) → ∃ u, stepSum S u = v := by
  first | exact @GlobalTheory.stepSum_surj_of_initial | exact GlobalTheory.stepSum_surj_of_initial | (intros; apply GlobalTheory.stepSum_surj_of_initial <;> assumption)
