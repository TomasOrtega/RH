import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanAutomorphismConjugatesOfNumberFieldIndepende

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjSpan.span_conj_eq_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSpanAutomorphismConjugatesOfNumberFieldIndepende.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.span_automorphismConjugates_of_numberField_independent_eq_top : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (e : ι → ℂ), (∀ c : ι → K, ∑ i, σ (c i) * e i = 0 → c = 0) → Submodule.span ℂ {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} = ⊤ := by
  first | exact @GlobalTheory.ConjSpan.span_conj_eq_top | exact GlobalTheory.ConjSpan.span_conj_eq_top | (intros; apply GlobalTheory.ConjSpan.span_conj_eq_top <;> assumption)
