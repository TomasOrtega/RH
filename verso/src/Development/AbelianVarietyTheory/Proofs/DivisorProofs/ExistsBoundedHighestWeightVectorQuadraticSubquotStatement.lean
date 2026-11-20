import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedHighestWeightVectorQuadraticSubquot
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsBoundedHighestWeightVectorQuadraticSubquot.lean&line=138#L138)
-/
theorem _root_.GlobalTheory.T.exists_boundedHighestWeightVector_quadraticSubquotient : ∀ (p q : ℕ) (α β α' β' : ℂ), ∃ B : ℚ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, N < N' → Stab act N → Stab act N' → QuadMod act α β α' β' N N' → ∃ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) ∧ ∃ v ∈ N', v ∈ hwSub act μ ∧ v ∉ N := by
  first | exact @GlobalTheory.HoweR.exists_hwSub_of_quadMod | exact GlobalTheory.HoweR.exists_hwSub_of_quadMod | (intros; apply GlobalTheory.HoweR.exists_hwSub_of_quadMod <;> assumption)
