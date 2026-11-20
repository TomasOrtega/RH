import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentral
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCentralIdempotentOfIrrCharacterOrthogonalCentral.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central : ∀ (G : Type) [Group G] [Fintype G] (χ χ' : G → ℂ), IsIrr χ → IsIrr χ' → (zOf χ * zOf χ' = if χ = χ' then zOf χ else 0) ∧ (∀ a, zOf χ * a = a * zOf χ) ∧ ip χ χ' = if χ = χ' then 1 else 0 := by
  first | exact @GlobalTheory.GLq.ZOrth.zorth | exact GlobalTheory.GLq.ZOrth.zorth | (intros; apply GlobalTheory.GLq.ZOrth.zorth <;> assumption)
