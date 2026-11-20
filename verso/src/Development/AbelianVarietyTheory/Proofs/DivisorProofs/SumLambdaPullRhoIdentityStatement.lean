import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLambdaPullRhoIdentity
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionForm.OneVec.Reassemble.sum_lam_pull_rho` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSumLambdaPullRhoIdentity.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.sum_lambda_pull_rho_identity : ∀ {n g : ℕ} (a : Fin n → ℂ) (w : Ext (1 + 1 + g)), ∑ S : Finset (Fin (1 + 1)), lamL S (pullFullL a (rhoL (n := n) S w)) = w := by
  first | exact @GlobalTheory.TorsionForm.OneVec.Reassemble.sum_lam_pull_rho | exact GlobalTheory.TorsionForm.OneVec.Reassemble.sum_lam_pull_rho | (intros; apply GlobalTheory.TorsionForm.OneVec.Reassemble.sum_lam_pull_rho <;> assumption)
