import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionRestrictionIsClassFunction
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHarishChandraInductionRestrictionIsClassFunction.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.harishChandra_induction_restriction_isClassFunction : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∀ Φ : Gn g a → Gn g b → ℂ, IsClass (hcT a b Φ n)) ∧ ∀ χ : Gn g n → ℂ, IsClass χ → (∀ h, IsClass (res a b χ h)) ∧ ∀ h, IsClass (fun x => res a b χ x h) := by
  first | exact @GlobalTheory.GLq.HcClass.hc_class | exact GlobalTheory.GLq.HcClass.hc_class | (intros; apply GlobalTheory.GLq.HcClass.hc_class <;> assumption)
