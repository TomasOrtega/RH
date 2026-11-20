import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogPeriodCongruenceBdr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Pst.StLat.log_trunc_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLogPeriodCongruenceBdr.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.log_period_congruence_bdr : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) → ∀ u : Per.BdRp l, IsLogP (beta ϖ) u →
  ∀ m : ℕ, 1 ≤ m → ∃ s ∈ Sg ϖ, ∃ e : Per.BdRp l, (e = 1 ∨ e = -1) ∧
    betaD ϖ ^ (2 * l ^ m) ∣ ((l : ℕ) : Per.BdRp l) * (((l : ℕ) : Per.BdRp l) ^ (m - 1) * u - s) - e * betaD ϖ ^ (l ^ m) := by
  first | exact @GlobalTheory.Pst.StLat.log_trunc_pow | exact GlobalTheory.Pst.StLat.log_trunc_pow | (intros; apply GlobalTheory.Pst.StLat.log_trunc_pow <;> assumption)
