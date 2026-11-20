import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AinfAdjoinBetaImageDivBetaPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FAinfAdjoinBetaImageDivBetaPow.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.ainfAdjoinBetaImage_div_beta_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ s ∈ Sg ϖ, ∀ i : ℕ, betaD ϖ ^ i ∣ s → ∃ s' ∈ Sg ϖ, s = betaD ϖ ^ i * s' := by
  first | exact @GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow | exact GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow | (intros; apply GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow <;> assumption)
