import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevel
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SymLevelExists.exists_isSymLevel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsIsSymmetricPositionLevel.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.exists_isSymmetricPositionLevel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ ρ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsSymLevel ψ ϖ ρ P := by
  first | exact @GlobalTheory.SymLevelExists.exists_isSymLevel | exact GlobalTheory.SymLevelExists.exists_isSymLevel | (intros; apply GlobalTheory.SymLevelExists.exists_isSymLevel <;> assumption)
