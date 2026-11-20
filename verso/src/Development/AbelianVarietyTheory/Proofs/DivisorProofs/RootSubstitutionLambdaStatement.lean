import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSubstitutionLambda
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRootSubstitutionLambda.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.root_substitution_lambda : ∀ (D : D7) (O : Setup D), aeval (GlobalTheory.RelabDR.rootSub O) (lamA D.what₂.Tau O.N O.j) = -∑ z, X z := by
  first | exact @GlobalTheory.RelabDR.aeval_rootSub_lamA | exact GlobalTheory.RelabDR.aeval_rootSub_lamA | (intros; apply GlobalTheory.RelabDR.aeval_rootSub_lamA <;> assumption)
