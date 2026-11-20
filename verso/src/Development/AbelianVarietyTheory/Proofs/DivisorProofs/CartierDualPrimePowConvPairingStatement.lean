import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualPrimePowConvPairing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCartierDualPrimePowConvPairing.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.cartierDual_primePow_conv_pairing : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n), (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  first | exact @GlobalTheory.Katz.cartier_primePow_pairing | exact GlobalTheory.Katz.cartier_primePow_pairing | (intros; apply GlobalTheory.Katz.cartier_primePow_pairing <;> assumption)
