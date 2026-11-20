import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGramMatrixResult.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.gram_matrix_result : GramSt := by
  first | exact @GlobalTheory.HalfGeo.gram | exact GlobalTheory.HalfGeo.gram | (intros; apply GlobalTheory.HalfGeo.gram <;> assumption)
