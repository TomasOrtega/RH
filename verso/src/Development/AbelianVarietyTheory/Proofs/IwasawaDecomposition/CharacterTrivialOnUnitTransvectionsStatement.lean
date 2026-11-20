import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnUnitTransvections
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCharacterTrivialOnUnitTransvections.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.character_trivial_on_unit_transvections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E), ξ ∈ X.Λ → ξ ≠ 0 → herm X.Gm ξ ξ = 0 → ∃ u : 𝓞 E, u ≠ 0 ∧ cc (u : E) = u ∧ ∀ t : E, cc t = t → IsIntegral ℤ t → ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * (u * t) * X.κ0) → φ γ = 1 := by
  first | exact @GlobalTheory.UnipKill.killsScaled | exact GlobalTheory.UnipKill.killsScaled | (intros; apply GlobalTheory.UnipKill.killsScaled <;> assumption)
