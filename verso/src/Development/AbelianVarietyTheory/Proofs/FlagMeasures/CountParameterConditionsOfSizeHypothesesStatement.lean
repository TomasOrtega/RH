import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountParameterConditionsOfSizeHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.CountT
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCountParameterConditionsOfSizeHypotheses.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.countParameterConditions_of_sizeHypotheses : ∀ (D : D7) (L : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (n0 : ℕ) (A C cb7 : ℝ), 0 ≤ C → 0 < cb7 → 2 * Cg ≤ A → (n0 : ℝ) ≤ D.R.k → 2 ≤ Cl → 2 * C ≤ Cl → Real.log L.sc.L ≤ cb7 * D.R.k → ArithmeticConditionsOfDatum D → StandingHypotheses D L C' Cl Cg cb Cu cT CT → AdmissibleBoundsFromSource.CountTheoremHypotheses D L n0 A C cb7 ∧ 4 * D.R.r < D.host.g 1 := by
  first | exact @GlobalTheory.countClauses_of_sizeHyp | exact GlobalTheory.countClauses_of_sizeHyp | (intros; apply GlobalTheory.countClauses_of_sizeHyp <;> assumption)
