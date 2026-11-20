import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingPairOfTuplesToTupleOfPairs
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsOpenEmbeddingPairOfTuplesToTupleOfPairs.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs : ∀ (κ X Y : Type) [Fintype κ] [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y], IsOpenEmbedding (zipHom κ X Y) := by
  first | exact @GlobalTheory.ModuLR.zipHom_isOpenEmbedding | exact GlobalTheory.ModuLR.zipHom_isOpenEmbedding | (intros; apply GlobalTheory.ModuLR.zipHom_isOpenEmbedding <;> assumption)
