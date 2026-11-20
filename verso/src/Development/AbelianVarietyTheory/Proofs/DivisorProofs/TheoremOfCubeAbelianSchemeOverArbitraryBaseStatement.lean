import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CubeTop.cubeTheorem | exact GlobalTheory.CubeTop.cubeTheorem | (intros; apply GlobalTheory.CubeTop.cubeTheorem <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base : GlobalTheory.Published.CubeTheorem := by
  first | exact @GlobalTheory.CubeTop.cubeTheorem | exact GlobalTheory.CubeTop.cubeTheorem | (intros; apply GlobalTheory.CubeTop.cubeTheorem <;> assumption)
