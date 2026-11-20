import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfMulLeftCharpolySeparable
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepGenElt.exists_aeval_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsAevalEqOfMulLeftCharpolySeparable.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  first | exact @GlobalTheory.SepGenElt.exists_aeval_eq | exact GlobalTheory.SepGenElt.exists_aeval_eq | (intros; apply GlobalTheory.SepGenElt.exists_aeval_eq <;> assumption)
