import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mass.MaxFormula.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMaximalHermitianLatticeMassRatio.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.maximalHermitianLattice_massRatio : MaxMass := by
  first | exact @GlobalTheory.Mass.MaxFormula.main | exact GlobalTheory.Mass.MaxFormula.main | (intros; apply GlobalTheory.Mass.MaxFormula.main <;> assumption)
