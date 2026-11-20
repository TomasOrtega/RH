import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchStepOfOneLeNorm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJacquetRallisUnitMatchStepOfOneLeNorm.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_step_of_one_le_norm : ∀ r : ℕ, UnitMatch r → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (M : Meas (r + 1) F E) (a : Inv (r + 1) F), Delta a ≠ 0 → 1 ≤ ‖mom (sec a) 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  first | exact @GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm | exact GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm | (intros; apply GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm <;> assumption)
