import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidSpanContinuousAutomorphicCuspidal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JSW.mspanR_cont_left_avg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCuspFormRapidSpanContinuousAutomorphicCuspidal.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1))
    (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → ∀ φ ∈ GlobalTheory.JSW.mspanR π, Continuous φ ∧
    (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) ∧
    ∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0 := by
  first | exact @GlobalTheory.JSW.mspanR_cont_left_avg | exact GlobalTheory.JSW.mspanR_cont_left_avg | (intros; apply GlobalTheory.JSW.mspanR_cont_left_avg; all_goals assumption)
