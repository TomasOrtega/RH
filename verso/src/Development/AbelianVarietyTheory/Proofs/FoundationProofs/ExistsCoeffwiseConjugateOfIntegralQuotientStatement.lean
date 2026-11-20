import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoeffwiseConjugateOfIntegralQuotient
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FN.conj_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsCoeffwiseConjugateOfIntegralQuotient.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.exists_coeffwiseConjugate_of_integral_quotient : ∀ (g : ℂ ≃+* ℂ) (N n : ℕ) (f D D' A A' : ℍ → ℂ) (s s' : Fin n → ℍ → ℂ), 0 < N → (∃ a, HasQ N f a) → QConj g N D D' → QConj g N A A' → (∀ j, QConj g N (s j) (s' j)) → D ≠ 0 → (∀ τ, f τ * D τ = A τ) → (∀ τ, f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ) = 0) → ∃ f' : ℍ → ℂ, QConj g N f f' ∧ ∀ τ, f' τ * D' τ = A' τ := by
  first | exact @GlobalTheory.FN.conj_exists | exact GlobalTheory.FN.conj_exists | (intros; apply GlobalTheory.FN.conj_exists <;> assumption)
