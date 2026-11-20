import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgue
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Amp.NLie.haarLie_eq_lebN` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHaarLieNilpotentEqLebesgue.lean&line=549#L549)
-/
theorem _root_.GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue : ∀ k r : ℕ, haarLie (Nset k r) 1 = (2 ^ (r * (k + 1) + r * (r - 1)) : ℝ≥0∞) • lebN k r := by
  first | exact @GlobalTheory.Amp.NLie.haarLie_eq_lebN | exact GlobalTheory.Amp.NLie.haarLie_eq_lebN | (intros; apply GlobalTheory.Amp.NLie.haarLie_eq_lebN <;> assumption)
