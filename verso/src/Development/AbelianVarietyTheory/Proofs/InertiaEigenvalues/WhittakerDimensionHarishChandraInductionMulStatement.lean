import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWhittakerDimensionHarishChandraInductionMul.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.whittakerDimension_harishChandraInduction_mul : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (a b n : ℕ), n = a + b → ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → wh ψ (hcT a b Φ n) = wh ψ (fun x => wh ψ (Φ x)) := by
  first | exact @GlobalTheory.GLq.WhMul.wh_hcT | exact GlobalTheory.GLq.WhMul.wh_hcT | (intros; apply GlobalTheory.GLq.WhMul.wh_hcT <;> assumption)
