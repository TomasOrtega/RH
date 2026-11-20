import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsPrimitiveTiltedRootOfUnityLocalPeriodRingsData.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsEps C.ε := by
  first | exact @GlobalTheory.MemLoc.core_isEps | exact GlobalTheory.MemLoc.core_isEps | (intros; apply GlobalTheory.MemLoc.core_isEps <;> assumption)
