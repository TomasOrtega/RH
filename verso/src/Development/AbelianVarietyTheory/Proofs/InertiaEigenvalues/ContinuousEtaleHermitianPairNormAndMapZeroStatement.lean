import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousEtaleHermitianPairNormAndMapZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.etale_norm_continuous_and_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FContinuousEtaleHermitianPairNormAndMapZero.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.continuous_etaleHermitianPair_norm_and_map_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Continuous A.NL ∧ A.NL 0 = 0 := by
  first | exact @GlobalTheory.etale_norm_continuous_and_zero | exact GlobalTheory.etale_norm_continuous_and_zero | (intros; apply GlobalTheory.etale_norm_continuous_and_zero <;> assumption)
