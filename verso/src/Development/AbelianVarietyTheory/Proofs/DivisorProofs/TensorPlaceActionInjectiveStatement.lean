import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPlaceActionInjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTensorPlaceActionInjective.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.tensor_place_action_injective : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : Type) [AddCommGroup V] [Module ℂ V] (J : Type)
    (L : J → Module.End ℂ V) (w₀ : ι), (∀ v : V, (∀ j, L j v = 0) → v = 0) →
    ∀ T : ⨂[ℂ] _ : ι, V, (∀ j, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ (L j) T = 0) → T = 0 := by
  first | exact @GlobalTheory.FactorKernel.atPl_noCommonKernel | exact GlobalTheory.FactorKernel.atPl_noCommonKernel | (intros; apply GlobalTheory.FactorKernel.atPl_noCommonKernel <;> assumption)
