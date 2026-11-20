import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickSetDensityLeInvFourLw
import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.thick_density_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThickSetDensityLeInvFourLw.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.thickSet_density_le_inv_four_Lw : ∀ (D : D7) (L : SizeData₂ D), 8 * D.host.Lw < D.R.n → L.de2 ≤ 1 / (4 * (D.host.Lw : ℝ)) := by
  first | exact @GlobalTheory.thick_density_le | exact GlobalTheory.thick_density_le | (intros; apply GlobalTheory.thick_density_le <;> assumption)
