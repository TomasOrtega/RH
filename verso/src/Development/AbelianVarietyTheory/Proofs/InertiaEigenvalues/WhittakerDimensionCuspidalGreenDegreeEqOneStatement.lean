import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOne
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLq.wh_cusp_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWhittakerDimensionCuspidalGreenDegreeEqOne.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → χ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) → wh ψ χ = 1 := by
  first | exact @GlobalTheory.GLq.wh_cusp_eq_one | exact GlobalTheory.GLq.wh_cusp_eq_one | (intros; apply GlobalTheory.GLq.wh_cusp_eq_one <;> assumption)
