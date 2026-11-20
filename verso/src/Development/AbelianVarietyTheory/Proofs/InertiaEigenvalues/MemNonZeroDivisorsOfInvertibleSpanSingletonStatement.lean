import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMemNonZeroDivisorsOfInvertibleSpanSingleton.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' : ∀ (A : Type) [CommRing A] (d : A), Module.Invertible A ↥(Ideal.span {d}) → d ∈ nonZeroDivisors A := by
  first | exact @GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton | exact GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton | (intros; apply GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton <;> assumption)
