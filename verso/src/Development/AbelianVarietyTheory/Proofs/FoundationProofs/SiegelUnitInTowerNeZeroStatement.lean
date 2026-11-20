import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZero
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSiegelUnitInTowerNeZero.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.siegelUnitInTower_ne_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ), admitted c x → siegel T c x ≠ 0 := by
  first | exact @GlobalTheory.KZ.siegel_ne_zero | exact GlobalTheory.KZ.siegel_ne_zero | (intros; apply GlobalTheory.KZ.siegel_ne_zero <;> assumption)
