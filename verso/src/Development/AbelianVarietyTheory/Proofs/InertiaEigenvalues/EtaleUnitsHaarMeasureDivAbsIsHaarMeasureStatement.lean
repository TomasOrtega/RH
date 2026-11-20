import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.LinDesc.unitsMeas_isHaar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEtaleUnitsHaarMeasureDivAbsIsHaarMeasure.lean&line=171#L171)
-/
theorem _root_.GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ, ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK := by
  first | exact @GlobalTheory.JR.LinDesc.unitsMeas_isHaar | exact GlobalTheory.JR.LinDesc.unitsMeas_isHaar | (intros; apply GlobalTheory.JR.LinDesc.unitsMeas_isHaar <;> assumption)
