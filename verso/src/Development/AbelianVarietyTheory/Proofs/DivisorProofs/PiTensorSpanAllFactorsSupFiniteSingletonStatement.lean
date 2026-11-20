import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSpanAllFactorsSupFiniteSingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweR.TensSup.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPiTensorSpanAllFactorsSupFiniteSingleton.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧ ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧ ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  first | exact @GlobalTheory.HoweR.TensSup.main | exact GlobalTheory.HoweR.TensSup.main | (intros; apply GlobalTheory.HoweR.TensSup.main <;> assumption)
