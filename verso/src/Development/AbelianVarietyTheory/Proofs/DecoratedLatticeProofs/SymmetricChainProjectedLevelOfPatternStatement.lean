import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPattern
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSymmetricChainProjectedLevelOfPattern.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.symmetricChain_projected_level_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.PrLevel t := by
  first | exact @GlobalTheory.SymChain.PrImage.prLevel_of_pattern | exact GlobalTheory.SymChain.PrImage.prLevel_of_pattern | (intros; apply GlobalTheory.SymChain.PrImage.prLevel_of_pattern <;> assumption)
