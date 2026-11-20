import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaIndependentOfEmbedding
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mean4.kap_indep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKappaIndependentOfEmbedding.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.kappa_independent_of_embedding : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (p : ℕ) (τ τ' : D.what₂.Tau), kap Y p τ = kap Y p τ' := by
  first | exact @GlobalTheory.Mean4.kap_indep | exact GlobalTheory.Mean4.kap_indep | (intros; apply GlobalTheory.Mean4.kap_indep <;> assumption)
