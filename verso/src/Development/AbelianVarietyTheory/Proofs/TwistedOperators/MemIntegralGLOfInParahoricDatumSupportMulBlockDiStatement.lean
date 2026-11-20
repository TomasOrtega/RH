import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntegralGLOfInParahoricDatumSupportMulBlockDi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMemIntegralGLOfInParahoricDatumSupportMulBlockDi.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.mem_integralGL_of_inParahoricDatumSupport_mul_blockDiag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (z : Matrix (A ⊕ E) (A ⊕ D) k) (x : GL A k) (y : GL D k),
    InSupp z → InSupp (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)) → x ∈ KO k A := by
  first | exact @GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp | exact GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp | (intros; apply GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp <;> assumption)
