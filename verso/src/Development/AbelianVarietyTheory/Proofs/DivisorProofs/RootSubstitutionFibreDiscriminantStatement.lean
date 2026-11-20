import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSubstitutionFibreDiscriminant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRootSubstitutionFibreDiscriminant.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.root_substitution_fibre_discriminant : ∀ (D : D7) (O : Setup D), GlobalTheory.GoodMetric.antisymm (aeval (GlobalTheory.RelabDR.rootSub O) (fibPt D.what₂.Tau O.N O.j)) = GlobalTheory.GoodMetric.rootDiscr O.S.Dw.mult := by
  first | exact @GlobalTheory.RelabDR.antisymm_fibPt | exact GlobalTheory.RelabDR.antisymm_fibPt | (intros; apply GlobalTheory.RelabDR.antisymm_fibPt <;> assumption)
