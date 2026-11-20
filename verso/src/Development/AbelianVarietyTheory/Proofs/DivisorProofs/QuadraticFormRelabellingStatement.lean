import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFormRelabelling
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuadraticFormRelabelling.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.quadratic_form_relabelling : ∀ (D : D7) (O : Setup D), aeval (fun i => (C (GlobalTheory.RelabDR.sg O i : ℝ) * X (GlobalTheory.RelabDR.ix O i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ)) (C (1 / 2 : ℝ) * ∑ l, X (Sum.inr l) ^ 2 - ∑ x, X (Sum.inl x) ^ 2 : MvPolynomial (GlobalTheory.EigWhole.Var O) ℝ) = ∑ z, X (Sum.inr z) ^ 2 - ∑ z, X (Sum.inl z) ^ 2 := by
  first | exact @GlobalTheory.RelabDR.aeval_halfWholeSq_sub_rootSq | exact GlobalTheory.RelabDR.aeval_halfWholeSq_sub_rootSq | (intros; apply GlobalTheory.RelabDR.aeval_halfWholeSq_sub_rootSq <;> assumption)
