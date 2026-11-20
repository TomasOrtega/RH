import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormUnits.norm_onto_units` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsMulStarEqOfNormOneUnramifiedQuadratic.lean&line=162#L162)
-/
theorem _root_.GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (u : F), ‖u‖ = 1 → ∃ v : E, v * star v = algebraMap F E u := by
  first | exact @GlobalTheory.NormUnits.norm_onto_units | exact GlobalTheory.NormUnits.norm_onto_units | (intros; apply GlobalTheory.NormUnits.norm_onto_units <;> assumption)
