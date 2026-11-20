import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDataExistenceOfSums
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFieldDataExistenceOfSums.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.field_data_existence_of_sums : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK → GlobalTheory.RowClaim.ConstK → (AtPt fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) → GlobalTheory.NormSum.IntSt → FieldDat → TorEx → DenEx → BotEx → BotSmall → Ex @Fld @Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.ex_of_claims | exact GlobalTheory.BigTop.Fun.ex_of_claims | (intros; apply GlobalTheory.BigTop.Fun.ex_of_claims <;> assumption)
