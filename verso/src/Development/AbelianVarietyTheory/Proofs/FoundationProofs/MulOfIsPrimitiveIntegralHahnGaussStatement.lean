import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGauss
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Glue.Prim.mul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMulOfIsPrimitiveIntegralHahnGauss.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω), Prim A P → Prim A Q → Prim A (P * Q) := by
  first | exact @GlobalTheory.Glue.Prim.mul | exact GlobalTheory.Glue.Prim.mul | (intros; apply GlobalTheory.Glue.Prim.mul <;> assumption)
