import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryPiFin
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweR.locU_pi_fin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsLocallyBlockUnitaryPiFin.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.isLocallyBlockUnitary_pi_fin : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), LocU s F → ∀ n : ℕ, LocU s (fun a b => (LinearMap.pi fun i : Fin n => F a b ∘ₗ LinearMap.proj i : Module.End ℂ (Fin n → M))) := by
  first | exact @GlobalTheory.HoweR.locU_pi_fin | exact GlobalTheory.HoweR.locU_pi_fin | (intros; apply GlobalTheory.HoweR.locU_pi_fin <;> assumption)
