import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLq.isCuspOf_label_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCuspidalCharacterLabelUniqueGLn.lean&line=263#L263)
-/
theorem _root_.GlobalTheory.T.cuspidalCharacter_label_unique_GLn : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → ∀ (d : ℕ) (P P' : (ZMod g)[X]) (χ χ' : Gn g d → ℂ), IsCuspOf L P χ → (IsCuspOf L P' χ → P = P') ∧ (Green → IsCuspOf L P χ' → χ = χ') := by
  first | exact @GlobalTheory.GLq.isCuspOf_label_unique | exact GlobalTheory.GLq.isCuspOf_label_unique | (intros; apply GlobalTheory.GLq.isCuspOf_label_unique <;> assumption)
