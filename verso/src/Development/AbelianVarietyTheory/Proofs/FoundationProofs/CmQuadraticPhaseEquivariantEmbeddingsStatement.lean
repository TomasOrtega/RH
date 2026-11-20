import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmQuadraticPhaseEquivariantEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QuadPhase.galPh1_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCmQuadraticPhaseEquivariantEmbeddings.lean&line=186#L186)
-/
theorem _root_.GlobalTheory.T.cmQuadraticPhase_equivariant_embeddings : ∀ D : D7, galPh1 D := by
  first | exact @GlobalTheory.QuadPhase.galPh1_all | exact GlobalTheory.QuadPhase.galPh1_all | (intros; apply GlobalTheory.QuadPhase.galPh1_all <;> assumption)
