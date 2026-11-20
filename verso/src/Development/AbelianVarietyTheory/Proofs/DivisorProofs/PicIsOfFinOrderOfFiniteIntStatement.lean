import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicIsOfFinOrderOfFiniteInt

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.pic_isOfFinOrder_of_finite_int | exact GlobalTheory.pic_isOfFinOrder_of_finite_int | (intros; apply GlobalTheory.pic_isOfFinOrder_of_finite_int <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.pic_isOfFinOrder_of_finite_int' : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  first | exact @GlobalTheory.pic_isOfFinOrder_of_finite_int | exact GlobalTheory.pic_isOfFinOrder_of_finite_int | (intros; apply GlobalTheory.pic_isOfFinOrder_of_finite_int <;> assumption)
