import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

/- English proof (translation)
Introduce `w hw`. Establish `hl0` using `l_ne_zero (K := K) l`. Establish `hlp` using `(Fact.out : l.Prime).pos`. Establish `hm : monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹) ∈ S O K e`. Use `monomial_mem_S ?_` and prove the remaining obligations.

Rewrite using `[norm_inv, norm_pow, inv_mul_le_one₀ (pow_pos (norm_pos_iff.2 hl0) _), wS, Nat.mul_div_cancel_left _ (NeZero.pos e)]`. Use `(norm_factorial_le l _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[pow_succ, Nat.mul_div_cancel _ hlp]`. Use `⟨_, P.MM.smul_mem ⟨_, hm⟩ hw, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (l : K) ^ (l ^ n) • ((monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹)) • w)`.

Rewrite using `[← smul_assoc, monomial_eq_C_mul_X_pow, smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one, one_mul]`.
-/
theorem PhiMod.exists_X_pow_smul_eq_l_pow_smul (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)
    (n : ℕ) : ∀ w ∈ P.MM, ∃ w' ∈ P.MM,
      (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  intro w hw
  have hl0 := l_ne_zero (K := K) l
  have hlp := (Fact.out : l.Prime).pos
  have hm : monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹) ∈ S O K e := by
    refine monomial_mem_S ?_
    rw [norm_inv, norm_pow, inv_mul_le_one₀ (pow_pos (norm_pos_iff.2 hl0) _), wS,
      Nat.mul_div_cancel_left _ (NeZero.pos e)]
    refine (norm_factorial_le l _).trans (le_of_eq ?_)
    rw [pow_succ, Nat.mul_div_cancel _ hlp]
  refine ⟨_, P.MM.smul_mem ⟨_, hm⟩ hw, ?_⟩
  change _ = (l : K) ^ (l ^ n) • ((monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹)) • w)
  rw [← smul_assoc, monomial_eq_C_mul_X_pow, smul_eq_C_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one, one_mul]
