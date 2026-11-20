import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantEqUnramifiedMulPeriod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMooreDeterminantEqUnramifiedMulPeriod.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.mooreDeterminant_eq_unramified_mul_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h → ∀ a : Fin h → P.R.B, (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) → (∀ (i : ℕ) j, ev P i (a j) ∈ Fil P 0) → (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ≠ 0 → P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ∈ Fil P 1 → ∃ κ : ↥(MaximalUnramifiedExtension l), κ ≠ 0 ∧ (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ * P.tB := by
  first | exact @GlobalTheory.PMon.mooreDeterminant_eq_unramified_mul_period_alt | exact GlobalTheory.PMon.mooreDeterminant_eq_unramified_mul_period_alt | (intros; apply GlobalTheory.PMon.mooreDeterminant_eq_unramified_mul_period_alt <;> assumption)
