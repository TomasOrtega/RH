import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseTransposeMemCuspFormRapidKernelSpanContra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FInverseTransposeMemCuspFormRapidKernelSpanContra.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.inverseTranspose_mem_cuspFormRapidKernelSpan_contragredient : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra := by
  first | exact @GlobalTheory.JSW.invT_mem_mspanR_contra | exact GlobalTheory.JSW.invT_mem_mspanR_contra | (intros; apply GlobalTheory.JSW.invT_mem_mspanR_contra <;> assumption)
