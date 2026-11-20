import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding : ∀ (F : Type) [NontriviallyNormedField F] (r : ℕ), Topology.IsClosedEmbedding (GlobalTheory.JR.Step.emb r F) := by
  first | exact @GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | exact GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | (intros; apply GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb <;> assumption)
