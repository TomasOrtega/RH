import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealEqOfNotLeMaximalMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FInvertibleIdealEqOfNotLeMaximalMul.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.eq_of_le_invertible_of_not_le_maximal_mul : ∀ (A : Type) [CommRing A] (I N : Ideal A), Module.Invertible A ↥I → N ≤ I → (∀ m : Ideal A, m.IsMaximal → ¬ N ≤ m * I) → N = I := by
  first | exact @GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul | exact GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul | (intros; apply GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul <;> assumption)
