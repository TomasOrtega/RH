import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnIntegralTransvections
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCharacterTrivialOnIntegralTransvections.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.character_trivial_on_integral_transvections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E) (s : E), ξ ∈ X.Λ → herm X.Gm ξ ξ = 0 → cc s = s → IsIntegral ℤ s → ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * s * X.κ0) → φ γ = 1 := by
  first | exact @GlobalTheory.UnipKill.killsTransv | exact GlobalTheory.UnipKill.killsTransv | (intros; apply GlobalTheory.UnipKill.killsTransv <;> assumption)
