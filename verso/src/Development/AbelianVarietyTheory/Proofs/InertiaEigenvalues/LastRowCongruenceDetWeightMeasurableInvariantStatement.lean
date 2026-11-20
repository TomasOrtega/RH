import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZUnfWt.wt_measurable_invariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLastRowCongruenceDetWeightMeasurableInvariant.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  first | exact @GlobalTheory.ZUnfWt.wt_measurable_invariant | exact GlobalTheory.ZUnfWt.wt_measurable_invariant | (intros; apply GlobalTheory.ZUnfWt.wt_measurable_invariant; all_goals assumption)
