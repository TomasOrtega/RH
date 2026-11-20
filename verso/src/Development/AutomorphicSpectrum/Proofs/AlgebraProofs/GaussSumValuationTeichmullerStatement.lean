import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussSumValuationTeichmuller
open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.GR.gauss_value` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FGaussSumValuationTeichmuller.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.gauss_sum_valuation_teichmuller : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → Fintype.card F ≠ 2 → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → ∀ ψ : AddChar F C, ψ ≠ 1 → v (∑ a, algebraMap R C (σ⁻¹ a) * ψ a) ^ (p - 1) = v (p : C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.gauss_value | exact GlobalTheory.CompanionTheory.Ar.GR.gauss_value | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.gauss_value <;> assumption)
