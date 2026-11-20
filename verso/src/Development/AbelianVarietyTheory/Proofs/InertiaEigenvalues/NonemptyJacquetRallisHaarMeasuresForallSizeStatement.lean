import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyJacquetRallisHaarMeasuresForallSize
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNonemptyJacquetRallisHaarMeasuresForallSize.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.nonempty_jacquetRallisHaarMeasures_forall_size : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by
  first | exact @GlobalTheory.JR.HaarExist.meas_nonempty | exact GlobalTheory.JR.HaarExist.meas_nonempty | (intros; apply GlobalTheory.JR.HaarExist.meas_nonempty <;> assumption)
