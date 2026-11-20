import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTower
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.gal_siegel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGaloisActionSiegelUnitInTower.lean&line=170#L170)
-/
theorem _root_.GlobalTheory.T.galois_action_siegelUnitInTower : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b d : ℕ) (s : Ω ≃ₐ[ℚ] Ω), 0 < M → a < M → s (eOm ε (1 / M)) = eOm ε (d / M) → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → T.gal s (siegel T c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel T c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] := by
  first | exact @GlobalTheory.KZ.gal_siegel | exact GlobalTheory.KZ.gal_siegel | (intros; apply GlobalTheory.KZ.gal_siegel <;> assumption)
