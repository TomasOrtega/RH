import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDetIdealSelfDualNormOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelDetIdealSelfDualNormOne.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.relDetIdeal_selfDual_normOne : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  first | exact @GlobalTheory.SelfDualDetNorm.detId_normOne | exact GlobalTheory.SelfDualDetNorm.detId_normOne | (intros; apply GlobalTheory.SelfDualDetNorm.detId_normOne <;> assumption)
