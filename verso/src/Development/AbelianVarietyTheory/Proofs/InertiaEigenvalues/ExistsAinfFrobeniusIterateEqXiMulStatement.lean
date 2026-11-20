import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfFrobeniusIterateEqXiMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PeriodSol.period_solution` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsAinfFrobeniusIterateEqXiMul.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.exists_ainf_frobenius_iterate_eq_xi_mul : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), GlobalTheory.MemLoc.IsEps e → ∀ n : ℕ, 0 < n → ∃ w : Per.Ainf l, GlobalTheory.MemLoc.xi e * w ≠ 0 ∧ (⇑(Per.φA l))^[n] w = GlobalTheory.MemLoc.xi e * w := by
  first | exact @GlobalTheory.PeriodSol.period_solution | exact GlobalTheory.PeriodSol.period_solution | (intros; apply GlobalTheory.PeriodSol.period_solution <;> assumption)
