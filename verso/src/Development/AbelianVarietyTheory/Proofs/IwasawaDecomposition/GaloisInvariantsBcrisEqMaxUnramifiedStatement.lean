import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramified
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.InvCris.invariants_Bcris` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGaloisInvariantsBcrisEqMaxUnramified.lean&line=164#L164)
-/
theorem _root_.GlobalTheory.T.galoisInvariants_Bcris_eq_maxUnramified : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.Bcris l), (∀ g ∈ GK K, Per.σB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ C.u c = b := by
  first | exact @GlobalTheory.MemLoc.InvCris.invariants_Bcris | exact GlobalTheory.MemLoc.InvCris.invariants_Bcris | (intros; apply GlobalTheory.MemLoc.InvCris.invariants_Bcris <;> assumption)
