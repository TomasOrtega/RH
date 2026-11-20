import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnSumTransvections
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnipKill.exists_mem_sum_transv_killed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCharacterTrivialOnSumTransvections.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.character_trivial_on_sum_transvections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (φ : X.Γ →* Multiplicative ℝ) (d : ℕ) (ξ : Fin d → Fin N → E) (α : Fin d → E), (∀ i j, herm X.Gm (ξ i) (ξ j) = 0) → (∀ j, ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm (ξ j) (α j) ∧ φ γ = 1) → ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 + ∑ j, α j • rk1 X.Gm (ξ j) (ξ j) ∧ φ γ = 1 := by
  first | exact @GlobalTheory.UnipKill.exists_mem_sum_transv_killed | exact GlobalTheory.UnipKill.exists_mem_sum_transv_killed | (intros; apply GlobalTheory.UnipKill.exists_mem_sum_transv_killed <;> assumption)
