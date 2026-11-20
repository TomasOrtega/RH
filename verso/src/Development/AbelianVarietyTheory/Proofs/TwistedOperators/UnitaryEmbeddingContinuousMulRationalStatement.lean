import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryEmbeddingContinuousMulRational.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.unitaryEmbedding_continuous_mul_rational : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), Continuous (stabilizerEmbedding d) ∧
    (∀ g h, stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h) ∧ ∀ γ ∈ GQ A, stabilizerEmbedding d γ ∈ GQ B := by
  first | exact @GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational | exact GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational | (intros; apply GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational <;> assumption)
