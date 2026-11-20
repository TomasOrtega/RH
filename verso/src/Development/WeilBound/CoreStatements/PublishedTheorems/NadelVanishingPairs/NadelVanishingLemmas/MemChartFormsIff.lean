import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemChartFormsIff
open GlobalTheory GlobalTheory.LogDR

/- English proof (citation)
Apply `GlobalTheory.LogDR.mem_chartForms_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemChartFormsIff.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.mem_chart_forms_iff : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) (η : abelian₂ K), η ∈ chartForms A x J t a ↔ ∃ c : Finset (Fin n) → K, (∀ I, I.card ≠ a → c I = 0) ∧ (∀ I, c I * t / ∏ j ∈ I \ J, (x j : K) ∈ A) ∧ η = ∑ I, c I • logWedge x I := by
  first | exact @_root_.GlobalTheory.LogDR.mem_chartForms_iff | exact _root_.GlobalTheory.LogDR.mem_chartForms_iff | (intros; apply _root_.GlobalTheory.LogDR.mem_chartForms_iff <;> assumption)
