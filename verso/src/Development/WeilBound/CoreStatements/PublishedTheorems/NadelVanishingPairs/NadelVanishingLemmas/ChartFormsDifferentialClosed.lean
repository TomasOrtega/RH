import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFormsDifferentialClosed
open GlobalTheory GlobalTheory.LogDR

/- English proof (citation)
Apply `GlobalTheory.LogDR.extD_mem_chartForms_twist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChartFormsDifferentialClosed.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.chart_forms_differential_closed : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ), AlgChart A x → ∀ q, ∀ η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) q, extD K η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) (q + 1) := by
  first | exact @_root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | exact _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | (intros; apply _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist <;> assumption)
