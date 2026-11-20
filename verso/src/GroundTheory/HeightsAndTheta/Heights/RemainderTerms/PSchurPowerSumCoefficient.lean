import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Introduce `N r k hk1 hkN nu hanti hsum`. Establish `hhom` using `h3 (Fin N) r nu`. Rewrite `hhom` using `[hsum]`. Take `⟨S, hS, hw⟩` from `h1 N k (schur (Fin N) nu) (Schur.schur_isSymmetric (σ := Fin N) nu) hhom`. Use `⟨S, hS, ?_⟩` and prove the remaining obligations.

Establish `e1` using `h2 N k hk1 hkN S hw`. Rewrite `e1` using `[hS, h4 N r k nu hk1 hkN hanti hsum]`. Establish `hk : (k : ℂ) ≠ 0` using `by exact_mod_cast (show k ≠ 0 by omega)`. Apply `Rat.cast_injective (α := ℂ)` to reduce the goal to its premises. Use `split_ifs with h`.

Rewrite `e1` using `[if_pos h]`. Use `push_cast`. Rewrite using `[eq_div_iff hk]`. Take the linear combination `-e1`. Rewrite `e1` using `[if_neg h]`.

Use `push_cast`. Break down `mul_eq_zero.mp e1.symm with h0 | h0` into its components or cases. Conclude with `absurd h0 hk`. Conclude with `h0`.
-/
theorem SchurPowerSumCoefficient.proof (h1 : SchWeightedPreimage.Statement)
    (h2 : SchEvalPowerSumHom.Statement) (h3 : SchSchurHomogeneous.Statement)
    (h4 : SchSchurAtRootsOfUnity.Statement) : SchurPowerSumCoefficient.Statement := by
  intro N r k hk1 hkN nu hanti hsum
  have hhom := h3 (Fin N) r nu
  rw [hsum] at hhom
  obtain ⟨S, hS, hw⟩ := h1 N k (schur (Fin N) nu) (Schur.schur_isSymmetric (σ := Fin N) nu) hhom
  refine ⟨S, hS, ?_⟩
  have e1 := h2 N k hk1 hkN S hw
  rw [hS, h4 N r k nu hk1 hkN hanti hsum] at e1
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  apply Rat.cast_injective (α := ℂ)
  split_ifs with h
  · rw [if_pos h] at e1
    push_cast
    rw [eq_div_iff hk]
    linear_combination -e1
  · rw [if_neg h] at e1
    push_cast
    rcases mul_eq_zero.mp e1.symm with h0 | h0
    · exact absurd h0 hk
    · exact h0

end

end GroundTheory.Heights₂.Heights.RestTerms
