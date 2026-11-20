import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists
open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FTeichmullerCharacterExists.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.teichmuller_character_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∃ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay | exact GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay <;> assumption)
