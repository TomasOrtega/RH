import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPos
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntBilinFormToRealMemPsdConeOfPos.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (id : ℤ → ℤ) (Fin r → ℤ) := by
  first | exact @GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | exact GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | (intros; apply GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int <;> assumption)
