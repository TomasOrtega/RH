import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ClassCountBoundAtConstructedPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScaleOneLeA
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberClosed

namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem h_la_all (𝒜 : FamClass) : H_la 𝒜 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ => ⟨Fm.x1 + 1, fun x hx i => GlobalTheory.famP_La_nonneg _ Fm x (by linarith) i⟩⟩⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classCountBound_all_classes (𝒜 : FamClass) : ClassCountBoundAllPoints 𝒜 :=
  GlobalTheory.ColClassNumber.classNumber_closed (W1 𝒜)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs and assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs and assume the hypotheses. A detailed English derivation is pending.
-/
theorem classCountBound_paramsLambda_constructedPoints : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), R0.ClassCountBoundAtConstructedPoints Q Lk ∧ R0.LambdaConditionAtConstructedPoints Q Lk := by
  intro Bd Q Lk
  refine ⟨?_, ?_⟩
  · apply Row.of_sel
    intros
    exact classCountBound_all_classes _
  · apply Row.of_sel
    intros
    exact h_la_all _

end GlobalTheory.Fc.R0
