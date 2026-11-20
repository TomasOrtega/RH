import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzIntegralMulStarNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArchimedeanSchwartzIntegralMulStarNeZero.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (f : SInf F κ), f ≠ 0 →
    (∫ x : κ → mixedEmbedding.mixedSpace F, f x * star (f x)) ≠ 0 := by
  first | exact @GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero | exact GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero | (intros; apply GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero <;> assumption)
