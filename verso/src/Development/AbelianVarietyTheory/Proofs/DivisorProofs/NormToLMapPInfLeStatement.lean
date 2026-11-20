import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormToLMapPInfLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLCuspNorm.norm_toL_map_pInf_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormToLMapPInfLe.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.norm_toL_map_pInf_le' : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ c : ℝ, 0 ≤ c ∧
    ∀ M : Matrix (Fin a) (Fin a) (Ad E),
      ‖toL (M.map (pInf E))‖ ≤ c * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a M‖ := by
  first | exact @GlobalTheory.GLCuspNorm.norm_toL_map_pInf_le | exact GlobalTheory.GLCuspNorm.norm_toL_map_pInf_le | (intros; apply GlobalTheory.GLCuspNorm.norm_toL_map_pInf_le <;> assumption)
