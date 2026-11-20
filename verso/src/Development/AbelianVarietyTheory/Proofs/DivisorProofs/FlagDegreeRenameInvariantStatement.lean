import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeRenameInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagDegreeRenameInvariant.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.flag_degree_rename_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (σ : Equiv.Perm ι) (F : Pol ι N), degFl ι N (rename (Prod.map σ id) F) = degFl ι N F := by
  first | exact @GlobalTheory.FlagPerm.degFl_rename_perm | exact GlobalTheory.FlagPerm.degFl_rename_perm | (intros; apply GlobalTheory.FlagPerm.degFl_rename_perm <;> assumption)
