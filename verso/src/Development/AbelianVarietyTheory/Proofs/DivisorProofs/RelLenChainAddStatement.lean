import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLenChainAdd
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.relLen_chain_add` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelLenChainAdd.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.relLen_trans_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ), RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  first | exact @GlobalTheory.relLen_chain_add | exact GlobalTheory.relLen_chain_add | (intros; apply GlobalTheory.relLen_chain_add <;> assumption)
