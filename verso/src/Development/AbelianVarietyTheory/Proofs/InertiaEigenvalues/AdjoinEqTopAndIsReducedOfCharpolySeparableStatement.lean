import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdjoinEqTopAndIsReducedOfCharpolySeparable.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.adjoin_eq_top_and_isReduced_of_charpoly_separable : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (y : A), (LinearMap.mulLeft E y).charpoly.Separable → Algebra.adjoin E ({y} : Set A) = ⊤ ∧ IsReduced A := by
  first | exact @GlobalTheory.SepGen.adjoin_eq_top_and_isReduced | exact GlobalTheory.SepGen.adjoin_eq_top_and_isReduced | (intros; apply GlobalTheory.SepGen.adjoin_eq_top_and_isReduced <;> assumption)
