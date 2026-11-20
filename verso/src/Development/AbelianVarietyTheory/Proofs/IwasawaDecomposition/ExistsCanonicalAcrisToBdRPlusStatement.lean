import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.exists_isCrisP` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCanonicalAcrisToBdRPlus.lean&line=210#L210)
-/
theorem _root_.GlobalTheory.T.exists_canonical_acris_to_bdRPlus : ∀ (l : ℕ) [Fact l.Prime], ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j := by
  first | exact @GlobalTheory.MemLoc.exists_isCrisP | exact GlobalTheory.MemLoc.exists_isCrisP | (intros; apply GlobalTheory.MemLoc.exists_isCrisP <;> assumption)
