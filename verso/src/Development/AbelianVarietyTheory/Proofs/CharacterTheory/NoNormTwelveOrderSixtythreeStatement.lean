import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormTwelveOrderSixtythree
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FNoNormTwelveOrderSixtythree.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 → ∑ k ∈ Finset.range 63, c k ^ 2 = 12 → (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j → ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_twelve_order_sixtythree | exact GlobalTheory.no_norm_twelve_order_sixtythree | (intros; apply GlobalTheory.no_norm_twelve_order_sixtythree <;> assumption)
