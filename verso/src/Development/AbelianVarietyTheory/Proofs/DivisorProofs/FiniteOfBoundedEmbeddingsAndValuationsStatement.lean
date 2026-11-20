import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedEmbeddingsAndValuations
import Mathlib
open NumberField IsDedekindDomain Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteOfBoundedEmbeddingsAndValuations.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.finite_of_bounded_embeddings_and_valuations : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by
  first | exact @GlobalTheory.BddFinite.finite_of_bdd | exact GlobalTheory.BddFinite.finite_of_bdd | (intros; apply GlobalTheory.BddFinite.finite_of_bdd <;> assumption)
