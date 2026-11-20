import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainSupportAtOfPattern
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SymSupportP.supportAt_of_pattern` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSymmetricLevelChainSupportAtOfPattern.lean&line=186#L186)
-/
theorem _root_.GlobalTheory.T.symmetricLevelChain_supportAt_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.SupportAt t := by
  first | exact @GlobalTheory.SymSupportP.supportAt_of_pattern | exact GlobalTheory.SymSupportP.supportAt_of_pattern | (intros; apply GlobalTheory.SymSupportP.supportAt_of_pattern <;> assumption)
