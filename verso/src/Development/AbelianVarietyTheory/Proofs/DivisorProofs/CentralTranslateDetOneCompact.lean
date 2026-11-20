import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalPairPowerSumVanish
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVerticalPairPowerSumVanish.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.central_translate_det_one_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (C : Set (GL (Fin N) k)), IsCompact C → ∃ D : Set (GL (Fin N) k), IsCompact D ∧ ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ c ∈ C, ValuativeRel.valuation k ((z * c : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 → z * c ∈ D := by
  first | exact @GlobalTheory.CentreCpt.exists_compact_center_mul | exact GlobalTheory.CentreCpt.exists_compact_center_mul | (intros; apply GlobalTheory.CentreCpt.exists_compact_center_mul <;> assumption)
