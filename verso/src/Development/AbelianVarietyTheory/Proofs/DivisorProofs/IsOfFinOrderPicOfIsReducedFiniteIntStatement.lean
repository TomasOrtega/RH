import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderPicOfIsReducedFiniteInt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PicReducedTors.pic_isOfFinOrder` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOfFinOrderPicOfIsReducedFiniteInt.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  first | exact @GlobalTheory.PicReducedTors.pic_isOfFinOrder | exact GlobalTheory.PicReducedTors.pic_isOfFinOrder | (intros; apply GlobalTheory.PicReducedTors.pic_isOfFinOrder <;> assumption)
