import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PadicResidueFieldCardAndPrimeIrreducible
import Mathlib
open ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TAdicInt.card_residueField_and_irreducible` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FPadicResidueFieldCardAndPrimeIrreducible.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.padic_residueField_card_and_prime_irreducible : ∀ (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[ℚ_[T]]) = T ∧ Irreducible ((T : 𝒪[ℚ_[T]])) := by
  first | exact @GlobalTheory.TAdicInt.card_residueField_and_irreducible | exact GlobalTheory.TAdicInt.card_residueField_and_irreducible | (intros; apply GlobalTheory.TAdicInt.card_residueField_and_irreducible <;> assumption)
