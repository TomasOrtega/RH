import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqInertiaDegAffineChart
import Mathlib
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FResidueDegreeEqInertiaDegAffineChart.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.residueDegree_eq_inertiaDeg_affine_chart : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  first | exact @GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | exact GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | (intros; apply GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg <;> assumption)
