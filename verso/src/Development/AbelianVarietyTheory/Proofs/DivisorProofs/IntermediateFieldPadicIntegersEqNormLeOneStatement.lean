import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntermediateFieldPadicIntegersEqNormLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameOf.intEmb_range_norm_le_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntermediateFieldPadicIntegersEqNormLeOne.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.intermediateField_padic_integers_eq_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] Lf], Function.Injective (intEmb Lf) ∧ ∀ x, x ∈ Set.range (intEmb Lf) ↔ x ∈ Lf ∧ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.FrameOf.intEmb_range_norm_le_one | exact GlobalTheory.FrameOf.intEmb_range_norm_le_one | (intros; apply GlobalTheory.FrameOf.intEmb_range_norm_le_one <;> assumption)
