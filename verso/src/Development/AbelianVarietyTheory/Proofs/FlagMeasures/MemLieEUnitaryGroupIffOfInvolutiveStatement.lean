import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLieEUnitaryGroupIffOfInvolutive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMemLieEUnitaryGroupIffOfInvolutive.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive : ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)), H * H = 1 → (x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0) := by
  first | exact @GlobalTheory.TubeLie.mem_lieE_UH_of_sq | exact GlobalTheory.TubeLie.mem_lieE_UH_of_sq | (intros; apply GlobalTheory.TubeLie.mem_lieE_UH_of_sq <;> assumption)
