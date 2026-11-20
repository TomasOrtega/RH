import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericLevelOfFrame
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenericLevel.exists_isGenericLevel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsGenericLevelOfFrame.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.exists_genericLevelOfFrame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsGenericLevel ψ ϖ P := by
  first | exact @GlobalTheory.GenericLevel.exists_isGenericLevel | exact GlobalTheory.GenericLevel.exists_isGenericLevel | (intros; apply GlobalTheory.GenericLevel.exists_isGenericLevel <;> assumption)
