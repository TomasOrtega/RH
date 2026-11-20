import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMonicSquarefreeUnitConstPolysIffMonicSquarefr
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadShare.mem_sqSet_iff` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMemMonicSquarefreeUnitConstPolysIffMonicSquarefr.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (f : (ZMod g)[X]), f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  first | exact @GlobalTheory.BadShare.mem_sqSet_iff | exact GlobalTheory.BadShare.mem_sqSet_iff | (intros; apply GlobalTheory.BadShare.mem_sqSet_iff <;> assumption)
