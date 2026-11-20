import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCoeffProdLinear
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpanCoeffProdLinear.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.span_coeff_prod_linear_eq_prod_span : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (d m : ℕ)
    (c : Fin d → Fin m → V),
    Ideal.span (Set.range fun s => (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by
  first | exact @GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear | exact GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear | (intros; apply GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear <;> assumption)
