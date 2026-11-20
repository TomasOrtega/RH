import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualPointsOfRowTies
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEventualPointsOfRowTies.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.eventual_points_of_row_ties : ∀ (prem : ∀ {eps : ℝ}, FamP eps → Prop) (G : PtP) (T : ℝ → ℝ → PtP), (Closed FamHyp fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ EvPt Fm fun x hx i p => G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p) → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW PRows 𝒜 σ → EvW (onPt G) 𝒜 σ → EvWC prem (fun C CH => onPt (T C CH)) 𝒜 σ := by
  first | exact @GlobalTheory.Fc.Ind.evWC_onPt_of_guarded | exact GlobalTheory.Fc.Ind.evWC_onPt_of_guarded | (intros; apply GlobalTheory.Fc.Ind.evWC_onPt_of_guarded <;> assumption)
