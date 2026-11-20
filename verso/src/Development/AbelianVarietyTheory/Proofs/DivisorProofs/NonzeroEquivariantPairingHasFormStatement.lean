import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroEquivariantPairingHasForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FockSplit.hasForm_of_pairing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonzeroEquivariantPairingHasForm.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.nonzero_equivariant_pairing_has_form : ∀ (P Q R S : ℕ) (x : ℚ) (b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ), b ≠ 0 → (∀ Z f g, b (fockAct1 P Q R 0 Z f) g + b f (fockAct1 P Q 0 S Z g) = (x : ℂ) * Z.trace * b f g) → GlobalTheory.RealLift.HasForm P Q R S x := by
  first | exact @GlobalTheory.FockSplit.hasForm_of_pairing | exact GlobalTheory.FockSplit.hasForm_of_pairing | (intros; apply GlobalTheory.FockSplit.hasForm_of_pairing <;> assumption)
