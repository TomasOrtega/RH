import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RankHostFacts.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwoLeHermitianRankAndHostDegreeEq.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  first | exact @GlobalTheory.RankHostFacts.main | exact GlobalTheory.RankHostFacts.main | (intros; apply GlobalTheory.RankHostFacts.main <;> assumption)
