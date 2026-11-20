import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FJacquetModuleMapInjectiveOfInjective.lean&line=168#L168)
-/
theorem _root_.GlobalTheory.T.jacquetModule_map_injective_of_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W) (f : π₁.IntertwiningMap π), IsSmooth π → Function.Injective f → Function.Injective (jacMap e f) := by
  first | exact @GlobalTheory.JacInj.jacMap_injective | exact GlobalTheory.JacInj.jacMap_injective | (intros; apply GlobalTheory.JacInj.jacMap_injective <;> assumption)
