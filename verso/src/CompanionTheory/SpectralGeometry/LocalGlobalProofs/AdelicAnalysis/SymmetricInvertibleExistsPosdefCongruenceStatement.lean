import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SymmetricInvertibleExistsPosdefCongruence
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FSymmetricInvertibleExistsPosdefCongruence.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.symmetric_invertible_exists_posdef_congruence : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 → ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | exact GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | (intros; apply GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm <;> assumption)
