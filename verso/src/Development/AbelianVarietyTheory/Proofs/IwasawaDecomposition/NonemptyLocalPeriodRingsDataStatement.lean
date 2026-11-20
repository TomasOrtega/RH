import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNonemptyLocalPeriodRingsData.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.nonempty_localPeriodRingsData : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Core l) := by
  first | exact @GlobalTheory.MemLoc.nonempty_core | exact GlobalTheory.MemLoc.nonempty_core | (intros; apply GlobalTheory.MemLoc.nonempty_core <;> assumption)
