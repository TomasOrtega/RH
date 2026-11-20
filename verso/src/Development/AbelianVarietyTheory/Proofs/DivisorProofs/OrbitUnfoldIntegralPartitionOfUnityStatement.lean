import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitUnfoldIntegralPartitionOfUnity
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOrbitUnfoldIntegralPartitionOfUnity.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.orbit_unfold_integral_partition_of_unity : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) → ∀ g : (I → ℝ) → ℂ, Integrable g → HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧ HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  first | exact @GlobalTheory.OrbitUnfold.orbit_unfold | exact GlobalTheory.OrbitUnfold.orbit_unfold | (intros; apply GlobalTheory.OrbitUnfold.orbit_unfold <;> assumption)
