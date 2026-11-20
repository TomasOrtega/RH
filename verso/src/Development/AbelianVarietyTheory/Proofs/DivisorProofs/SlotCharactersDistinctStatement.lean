import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockCharactersDistinct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeviBlockCharactersDistinct.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.position_characters_distinct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), 2 * n ≠ d → IsUnitaryChar ν → ∀ i i' j j' : Fin 2, (i ≠ j ∨ i' ≠ j') →
    ∃ p : kˣ × kˣ, cellChar₂ k (b2 n d) (chi2 k ν) i i' p ≠ cellChar₂ k (b2 n d) (chi2 k ν) j j' p := by
  first | exact @GlobalTheory.IndJacBlock.cellChar_distinct | exact GlobalTheory.IndJacBlock.cellChar_distinct | (intros; apply GlobalTheory.IndJacBlock.cellChar_distinct <;> assumption)
