import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPartOfClassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Formalism.LocalRingCardinality.DataNChTie
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormalizedPartOfClassSum.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.normalized_part_of_class_sum : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Part D O c), PDiv D O c b → GlobalTheory.ExportPin.ClassSumPin b.pt → PNmj D O c b := by
  first | exact @GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin | exact GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin | (intros; apply GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin <;> assumption)
