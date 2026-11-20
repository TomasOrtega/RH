import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassDegTypeLeCycleType
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadShare.mass_degType_le_cycleType` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMassDegTypeLeCycleType.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.mass_degType_le_card_cycleType_div : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (A : Multiset ℕ → Prop), (mass g N fun f => A (degType g f)) ≤ ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => A σ.partition.parts).card : ℝ) / (N.factorial : ℝ) := by
  first | exact @GlobalTheory.BadShare.mass_degType_le_cycleType | exact GlobalTheory.BadShare.mass_degType_le_cycleType | (intros; apply GlobalTheory.BadShare.mass_degType_le_cycleType <;> assumption)
