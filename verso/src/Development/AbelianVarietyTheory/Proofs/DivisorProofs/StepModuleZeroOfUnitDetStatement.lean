import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepModuleZeroOfUnitDet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepInclStepProj
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.FlagChi Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStepModuleZeroOfUnitDet.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.step_module_zero_of_unit_det : ∀ (Z : Scheme.{0}) [IsIntegral Z] (N : ℕ) (M : Matrix (Fin N) (Fin N) Z.functionField), IsUnit M.det → Limits.IsZero (stepMod M 0) := by
  first | exact @GlobalTheory.FlagChi.isZero_stepMod_zero | exact GlobalTheory.FlagChi.isZero_stepMod_zero | (intros; apply GlobalTheory.FlagChi.isZero_stepMod_zero <;> assumption)
