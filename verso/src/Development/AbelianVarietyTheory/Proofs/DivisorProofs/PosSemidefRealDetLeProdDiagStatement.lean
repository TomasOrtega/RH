import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefRealDetLeProdDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPosSemidefRealDetLeProdDiag.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.posSemidef_det_le_prod_diag' : ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → G.det ≤ ∏ i, G i i := by
  first | exact @GlobalTheory.posSemidef_real_det_le_prod_diag | exact GlobalTheory.posSemidef_real_det_le_prod_diag | (intros; apply GlobalTheory.posSemidef_real_det_le_prod_diag <;> assumption)
