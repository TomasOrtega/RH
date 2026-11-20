import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIntegrableOnAbsDetRpowLeOneFundamentalDomain.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ s : ℝ, 0 < s → IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ s) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  first | exact @GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low | exact GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low | (intros; apply GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low <;> assumption)
