import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelRowsEqDimensionAll
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBaseLevelRowsEqDimensionAll.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.base_level_rows_eq_dimension_all : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Part D O c), BaseRankDimension D O c b := by
  first | exact @GlobalTheory.Fc.Ind.base_level_rows_eq_dimension | exact GlobalTheory.Fc.Ind.base_level_rows_eq_dimension | (intros; apply GlobalTheory.Fc.Ind.base_level_rows_eq_dimension <;> assumption)
