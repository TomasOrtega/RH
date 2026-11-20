import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicIsOfFinOrderOfFiniteInt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.pic_isOfFinOrder_of_finite_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPicIsOfFinOrderOfFiniteInt.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.pic_isOfFinOrder_of_finite_int' : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  first | exact @GlobalTheory.pic_isOfFinOrder_of_finite_int | exact GlobalTheory.pic_isOfFinOrder_of_finite_int | (intros; apply GlobalTheory.pic_isOfFinOrder_of_finite_int <;> assumption)
