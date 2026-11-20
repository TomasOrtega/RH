import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweR.fock_locU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFockActionIsLocallyBlockUnitary.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.fockAction_isLocallyBlockUnitary : ∀ P Q R S : ℕ, LocU (fun a : Ix R S => a.isLeft) (units (fockAct2 P Q R S)) := by
  first | exact @GlobalTheory.HoweR.fock_locU | exact GlobalTheory.HoweR.fock_locU | (intros; apply GlobalTheory.HoweR.fock_locU <;> assumption)
