import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionIsLieAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.SteepMult.TLie.isKLieAct_tAct | exact GlobalTheory.SteepMult.TLie.isKLieAct_tAct | (intros; apply GlobalTheory.SteepMult.TLie.isKLieAct_tAct <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.tensor_action_is_lie_action : ∀ (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W),
    IsKLieAct actW → IsKLieAct (tAct k actW) := by
  first | exact @GlobalTheory.SteepMult.TLie.isKLieAct_tAct | exact GlobalTheory.SteepMult.TLie.isKLieAct_tAct | (intros; apply GlobalTheory.SteepMult.TLie.isKLieAct_tAct <;> assumption)
