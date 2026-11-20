import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodGlRepPiTensorActionAtFactorAndCommute
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweR.actAt_good_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsGoodGlRepPiTensorActionAtFactorAndCommute.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.isGoodGlRep_piTensorActionAtFactor_and_commute : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)), (∀ w, Good (a w)) → (∀ w, Good (actAt w (a w))) ∧ ∀ w w', w ≠ w' → ∀ Z Z' v, actAt w (a w) Z (actAt w' (a w') Z' v) = actAt w' (a w') Z' (actAt w (a w) Z v) := by
  first | exact @GlobalTheory.HoweR.actAt_good_comm | exact GlobalTheory.HoweR.actAt_good_comm | (intros; apply GlobalTheory.HoweR.actAt_good_comm <;> assumption)
