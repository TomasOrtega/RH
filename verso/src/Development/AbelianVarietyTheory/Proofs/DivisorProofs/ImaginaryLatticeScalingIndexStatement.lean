import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImaginaryLatticeScalingIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LieDisc.relIndex_mulLeft_imLat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FImaginaryLatticeScalingIndex.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.imaginary_lattice_scaling_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), Unr E → 1 ≤ r → (AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E)).relIndex (imLat E) = r ^ fdeg E := by
  first | exact @GlobalTheory.LieDisc.relIndex_mulLeft_imLat | exact GlobalTheory.LieDisc.relIndex_mulLeft_imLat | (intros; apply GlobalTheory.LieDisc.relIndex_mulLeft_imLat <;> assumption)
