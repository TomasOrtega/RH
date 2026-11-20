import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoverKGen.kset_gen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDoubleCoverUpqKsetGeneratedByExp.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.doubleCoverUpq_Kset_generated_by_exp : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q), ∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) := by
  first | exact @GlobalTheory.CoverKGen.kset_gen | exact GlobalTheory.CoverKGen.kset_gen | (intros; apply GlobalTheory.CoverKGen.kset_gen <;> assumption)
