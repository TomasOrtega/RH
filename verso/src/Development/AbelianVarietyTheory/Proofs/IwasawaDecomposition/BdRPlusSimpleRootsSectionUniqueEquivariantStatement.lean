import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusSimpleRootsSectionUniqueEquivariant
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.SecUniq.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBdRPlusSimpleRootsSectionUniqueEquivariant.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → (∀ (x : Om l) (y : Per.BdRp l) (f : Polynomial (Om l)), Per.θD l y = (x : ℂ_[l]) → f.eval x = 0 → f.derivative.eval x ≠ 0 → (f.map o).eval y = 0 → y = o x) ∧ (∀ o' : Om l →+* Per.BdRp l, IsSec o' → o' = o) ∧ ∀ (g : Per.Gq l) (x : Om l), Per.σDp g (o x) = o (g x) := by
  first | exact @GlobalTheory.MemLoc.SecUniq.main | exact GlobalTheory.MemLoc.SecUniq.main | (intros; apply GlobalTheory.MemLoc.SecUniq.main <;> assumption)
