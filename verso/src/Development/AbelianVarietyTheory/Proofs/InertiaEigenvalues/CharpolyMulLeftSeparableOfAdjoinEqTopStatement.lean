import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMulLeftSeparableOfAdjoinEqTop
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCharpolyMulLeftSeparableOfAdjoinEqTop.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.charpoly_mulLeft_separable_of_adjoin_eq_of_reduced : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A] [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A → (LinearMap.mulLeft E y).charpoly.Separable := by
  first | exact @GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top | exact GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top | (intros; apply GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top <;> assumption)
