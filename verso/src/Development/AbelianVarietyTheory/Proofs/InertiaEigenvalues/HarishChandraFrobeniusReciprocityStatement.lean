import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocity
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHarishChandraFrobeniusReciprocity.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.harishChandra_frobenius_reciprocity : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ), IsClass χ → ip χ (hcT a b Φ n) = ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) := by
  first | exact @GlobalTheory.GLq.FrobRecHC.hcT_adjoint | exact GlobalTheory.GLq.FrobRecHC.hcT_adjoint | (intros; apply GlobalTheory.GLq.FrobRecHC.hcT_adjoint <;> assumption)
