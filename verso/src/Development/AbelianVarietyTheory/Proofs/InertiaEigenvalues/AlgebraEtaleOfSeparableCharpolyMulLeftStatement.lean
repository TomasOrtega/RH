import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeft
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.etale_of_separable_charpoly_mulLeft` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAlgebraEtaleOfSeparableCharpolyMulLeft.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Algebra.Etale E A := by
  first | exact @GlobalTheory.etale_of_separable_charpoly_mulLeft | exact GlobalTheory.etale_of_separable_charpoly_mulLeft | (intros; apply GlobalTheory.etale_of_separable_charpoly_mulLeft <;> assumption)
