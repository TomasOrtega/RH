import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteIrrCharactersAndFinsumCentralIdempotentsEq.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one : ∀ (G : Type) [Group G] [Fintype G] , {χ : G → ℂ | IsIrr χ}.Finite ∧ ∑ᶠ χ ∈ {χ : G → ℂ | IsIrr χ}, zOf χ = 1 := by
  first | exact @GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one | exact GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one | (intros; apply GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one <;> assumption)
