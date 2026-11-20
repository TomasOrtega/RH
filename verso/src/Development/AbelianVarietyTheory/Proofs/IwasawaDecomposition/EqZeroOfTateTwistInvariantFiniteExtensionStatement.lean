import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.tate_twist_invariants` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FEqZeroOfTateTwistInvariantFiniteExtension.lean&line=302#L302)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (i : ℤ) (x : ℂ_[l]), i ≠ 0 → (∀ g ∈ GK K, Per.σC g x * (algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l])) ^ i = x) → x = 0 := by
  first | exact @GlobalTheory.MemLoc.tate_twist_invariants | exact GlobalTheory.MemLoc.tate_twist_invariants | (intros; apply GlobalTheory.MemLoc.tate_twist_invariants <;> assumption)
