import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.LinDesc.tm_isClosedEmbedding` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  first | exact @GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | exact GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | (intros; apply GlobalTheory.JR.LinDesc.tm_isClosedEmbedding <;> assumption)
