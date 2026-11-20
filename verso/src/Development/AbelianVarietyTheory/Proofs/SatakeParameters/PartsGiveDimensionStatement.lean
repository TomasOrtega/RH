import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimension
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NRows.Parts.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FPartsGiveDimension.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.parts_give_dimension : ∀ D : D7, GlobalTheory.NRows.PartsGive D := by
  first | exact @GlobalTheory.NRows.Parts.main | exact GlobalTheory.NRows.Parts.main | (intros; apply GlobalTheory.NRows.Parts.main <;> assumption)
