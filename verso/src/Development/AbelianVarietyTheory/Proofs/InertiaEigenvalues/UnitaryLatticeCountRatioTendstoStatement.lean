import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendsto
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.unitaryLimit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitaryLatticeCountRatioTendsto.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.unitary_lattice_count_ratio_tendsto : UnitaryLimit := by
  first | exact @GlobalTheory.UnitLemma.unitaryLimit | exact GlobalTheory.UnitLemma.unitaryLimit | (intros; apply GlobalTheory.UnitLemma.unitaryLimit <;> assumption)
