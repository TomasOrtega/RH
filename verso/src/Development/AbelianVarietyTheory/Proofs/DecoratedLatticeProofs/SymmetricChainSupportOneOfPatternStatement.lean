import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSymmetricChainSupportOneOfPattern.lean&line=240#L240)
-/
theorem _root_.GlobalTheory.T.symmetricChain_supportOne_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.SupportOne t := by
  first | exact @GlobalTheory.SymSupport.supportOne_of_pattern | exact GlobalTheory.SymSupport.supportOne_of_pattern | (intros; apply GlobalTheory.SymSupport.supportOne_of_pattern <;> assumption)
