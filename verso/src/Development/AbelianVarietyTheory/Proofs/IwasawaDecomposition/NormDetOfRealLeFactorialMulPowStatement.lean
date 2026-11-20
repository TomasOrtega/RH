import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDetOfRealLeFactorialMulPow
import Mathlib
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNormDetOfRealLeFactorialMulPow.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.norm_det_ofReal_le_factorial_mul_pow : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef → (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  first | exact @GlobalTheory.det_map_ofReal_norm_le | exact GlobalTheory.det_map_ofReal_norm_le | (intros; apply GlobalTheory.det_map_ofReal_norm_le <;> assumption)
