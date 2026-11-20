import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ClassCountBoundAtConstructedPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScaleOneLeA
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberClosed

namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨Fm.x1 + 1, fun x hx i => GlobalTheory.famP_La_nonneg _ Fm x (by linarith) i⟩⟩⟩`.
-/
theorem h_la_all (𝒜 : FamClass) : H_la 𝒜 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ => ⟨Fm.x1 + 1, fun x hx i => GlobalTheory.famP_La_nonneg _ Fm x (by linarith) i⟩⟩⟩

/- English proof (translation)
The claim follows from `GlobalTheory.ColClassNumber.classNumber_closed (W1 𝒜)`.
-/
theorem classCountBound_all_classes (𝒜 : FamClass) : ClassCountBoundAllPoints 𝒜 :=
  GlobalTheory.ColClassNumber.classNumber_closed (W1 𝒜)

/- English proof (translation)
Introduce `Bd Q Lk`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `Row.of_sel` to reduce the goal to its premises. Use `intros`. Conclude with `classCountBound_all_classes _`.

Apply `Row.of_sel` to reduce the goal to its premises. Use `intros`. Conclude with `h_la_all _`.
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
