import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsHaarProbabilityMaxCompactHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsIsHaarProbabilityMaxCompactHermitian.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.exists_isHaarProbabilityMaxCompactHermitian : ∀ k r : ℕ, ∃ μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), GlobalTheory.KFinAvg.IsHaarKH k r μ := by
  first | exact @GlobalTheory.KFinAvg.exists_isHaarKH | exact GlobalTheory.KFinAvg.exists_isHaarKH | (intros; apply GlobalTheory.KFinAvg.exists_isHaarKH <;> assumption)
