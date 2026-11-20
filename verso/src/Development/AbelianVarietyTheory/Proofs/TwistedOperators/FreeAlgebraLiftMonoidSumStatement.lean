import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FreeAlgebraLiftMonoidSum
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFreeAlgebraLiftMonoidSum.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.freeAlgebra_lift_monoid_sum : ∀ {B : Type} [Ring B] [Algebra ℂ B] {X : Type} (f : X → B) (p : FreeAlgebra ℂ X), FreeAlgebra.lift ℂ f p = Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff fun (w : FreeMonoid X) (c : ℂ) => c • (w.toList.map f).prod := by
  first | exact @GlobalTheory.freeAlgebra_lift_eq_sum_monomials | exact GlobalTheory.freeAlgebra_lift_eq_sum_monomials | (intros; apply GlobalTheory.freeAlgebra_lift_eq_sum_monomials <;> assumption)
