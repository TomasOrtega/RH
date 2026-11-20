import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardIrreducibleSamePrimeToPartRootsLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCardIrreducibleSamePrimeToPartRootsLe.lean&line=152#L152)
-/
theorem _root_.GlobalTheory.T.card_irreducible_samePrimeToPart_roots_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N d l : ℕ), 2 ≤ d → d ≤ N → l.Prime → ¬ BB g N l → (((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card : ℝ) ≤ (g : ℝ) ^ ((3 * d : ℝ) / 4) := by
  first | exact @GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le | exact GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le | (intros; apply GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le <;> assumption)
