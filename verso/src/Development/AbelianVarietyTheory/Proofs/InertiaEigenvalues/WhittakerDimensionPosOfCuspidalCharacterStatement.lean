import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionPosOfCuspidalCharacter
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWhittakerDimensionPosOfCuspidalCharacter.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.whittakerDimension_pos_of_cuspidal_character : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := by
  first | exact @GlobalTheory.GLq.wh_cusp_pos | exact GlobalTheory.GLq.wh_cusp_pos | (intros; apply GlobalTheory.GLq.wh_cusp_pos <;> assumption)
