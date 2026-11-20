import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjective
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAlgebraMapAinfInvPrimeBdRPlusInjective.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  first | exact @GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective | exact GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective | (intros; apply GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective <;> assumption)
