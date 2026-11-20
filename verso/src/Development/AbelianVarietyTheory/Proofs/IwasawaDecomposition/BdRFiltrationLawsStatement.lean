import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.filD_laws` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBdRFiltrationLaws.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.bdR_filtration_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ a : ℤ, Per.FilD l (a + 1) ≤ Per.FilD l a) ∧ (1 : Per.BdR l) ∈ Per.FilD l 0 ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ x : Per.BdR l, ∃ a, x ∈ Per.FilD l a) ∧ (∀ x : Per.BdR l, (∀ a, x ∈ Per.FilD l a) → x = 0) ∧ (∀ (g : Per.Gq l) (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a → Per.σD g x ∈ Per.FilD l a) ∧ ∀ (n : ℕ) (y : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
  first | exact @GlobalTheory.MemLoc.filD_laws | exact GlobalTheory.MemLoc.filD_laws | (intros; apply GlobalTheory.MemLoc.filD_laws <;> assumption)
