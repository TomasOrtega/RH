import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CLTateInvariantsFiniteExtensionMem
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCLTateInvariantsFiniteExtensionMem.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.cLTate_invariants_finiteExtension_mem : ∀ (l : ℕ) [Fact l.Prime], ∀ (K : FinExt l) (x : ℂ_[l]), (∀ g ∈ GK K, Per.σC g x = x) → ∃ y ∈ K.1, ((y : Om l) : ℂ_[l]) = x := by
  first | exact @GlobalTheory.MemLoc.invariants_finExt | exact GlobalTheory.MemLoc.invariants_finExt | (intros; apply GlobalTheory.MemLoc.invariants_finExt <;> assumption)
