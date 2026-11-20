import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PtSt.reducedMultiplicity_of_rows` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FReducedFormOfLocalInputs.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.reduced_form_of_local_inputs : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → GlobalTheory.NRows.Rows D → SumRepresentations.ReducedMultiplicityStatement D := by
  first | exact @GlobalTheory.PtSt.reducedMultiplicity_of_rows | exact GlobalTheory.PtSt.reducedMultiplicity_of_rows | (intros; apply GlobalTheory.PtSt.reducedMultiplicity_of_rows <;> assumption)
