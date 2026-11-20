import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiPullBaseComm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPhiPullBaseComm.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.phi_pull_base_comm : ∀ {n : ℕ} (a : Fin n → ℂ) (y : Ext (n + n)), phi (pullBaseL a y) = pullBaseL a (phi y) := by
  first | exact @GlobalTheory.TorsionForm.OneVec.phi_pullBaseL | exact GlobalTheory.TorsionForm.OneVec.phi_pullBaseL | (intros; apply GlobalTheory.TorsionForm.OneVec.phi_pullBaseL <;> assumption)
