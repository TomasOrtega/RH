import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.GR.FundGen.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FTeichmullerCharacterOrderGenerates.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.teichmuller_character_order_generates : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → orderOf σ = p ^ f - 1 ∧ (∀ χ : MulChar F R, ∃ m, 1 ≤ m ∧ m ≤ p ^ f - 1 ∧ χ = σ ^ m) ∧ (∀ n, (∀ a b, (σ ^ p ^ n) (a + b) - (σ ^ p ^ n) a - (σ ^ p ^ n) b ∈ Ideal.span {(p : R)})) ∧ (∀ τ : MulChar F R, (∀ a b, τ (a + b) - τ a - τ b ∈ Ideal.span {(p : R)}) → ∃ n < f, τ = σ ^ p ^ n) ∧ (∀ a b : F, a ≠ b → v (algebraMap R C (σ a - σ b)) = 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.FundGen.main | exact GlobalTheory.CompanionTheory.Ar.GR.FundGen.main | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.FundGen.main <;> assumption)
