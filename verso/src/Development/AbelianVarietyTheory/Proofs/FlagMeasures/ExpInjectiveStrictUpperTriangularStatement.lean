import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpInjectiveStrictUpperTriangular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ExpStrictUpper.exp_inj_strictUpper` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExpInjectiveStrictUpperTriangular.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.exp_injective_strictUpperTriangular : ∀ (m : ℕ) (X Y : Matrix (Fin m) (Fin m) ℂ), (∀ i j, j ≤ i → X i j = 0) → (∀ i j, j ≤ i → Y i j = 0) → NormedSpace.exp X = NormedSpace.exp Y → X = Y := by
  first | exact @GlobalTheory.ExpStrictUpper.exp_inj_strictUpper | exact GlobalTheory.ExpStrictUpper.exp_inj_strictUpper | (intros; apply GlobalTheory.ExpStrictUpper.exp_inj_strictUpper <;> assumption)
