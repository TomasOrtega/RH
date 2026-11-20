import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthTensorProductFactors
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHoweFiniteLengthTensorProductFactors.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.howe_finite_length_tensor_product_factors : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)), (∀ w, Pack (a w) (C w)) → HoweAlg (fun w => actAt w (a w)) (tensAny C) := by
  first | exact @GlobalTheory.HoweR.howeAlg_tensAny | exact GlobalTheory.HoweR.howeAlg_tensAny | (intros; apply GlobalTheory.HoweR.howeAlg_tensAny <;> assumption)
