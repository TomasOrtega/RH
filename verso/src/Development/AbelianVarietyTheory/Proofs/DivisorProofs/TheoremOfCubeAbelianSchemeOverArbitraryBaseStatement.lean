import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTheoremOfCubeAbelianSchemeOverArbitraryBase.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base : GlobalTheory.Published.CubeTheorem := by
  first | exact @GlobalTheory.CubeTop.cubeTheorem | exact GlobalTheory.CubeTop.cubeTheorem | (intros; apply GlobalTheory.CubeTop.cubeTheorem <;> assumption)
