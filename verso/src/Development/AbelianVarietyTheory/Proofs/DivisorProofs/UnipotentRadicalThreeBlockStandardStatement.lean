import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalThreeBlockStandard
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnipotentRadicalThreeBlockStandard.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.unipotent_radical_three_block_standard : ∀ (k : Type) [Field k] (d : ℕ) (h2 : 2 ≤ d) (u : GL (Fin d) k),
    u ∈ unipRad k (place3 h2) → GlobalTheory.JacBlock₂.IsUnipStd u := by
  first | exact @GlobalTheory.UnipRadThree.isUnipStd_of_mem_unipRad | exact GlobalTheory.UnipRadThree.isUnipStd_of_mem_unipRad | (intros; apply GlobalTheory.UnipRadThree.isUnipStd_of_mem_unipRad <;> assumption)
