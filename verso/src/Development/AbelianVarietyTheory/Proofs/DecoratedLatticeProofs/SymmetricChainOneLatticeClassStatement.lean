import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneLatticeClass
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SymChain.LatClass.oneClass_symChain` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSymmetricChainOneLatticeClass.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.symmetricChain_oneLatticeClass : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneClass t ν := by
  first | exact @GlobalTheory.SymChain.LatClass.oneClass_symChain | exact GlobalTheory.SymChain.LatClass.oneClass_symChain | (intros; apply GlobalTheory.SymChain.LatClass.oneClass_symChain <;> assumption)
