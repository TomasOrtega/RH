import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjective
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAinfIsDomainAndAinfInvPInjective.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.usage : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.Ainf l) ∧ IsDomain (Per.AinfP l) ∧ Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
  first | exact @GlobalTheory.MemLoc.ainf_isDomain_and_injective | exact GlobalTheory.MemLoc.ainf_isDomain_and_injective | (intros; apply GlobalTheory.MemLoc.ainf_isDomain_and_injective <;> assumption)
