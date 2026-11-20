import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHookFactorBranch
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVandermondeBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

/- English proof (translation)
Introduce `j u`. Use `set v : Fin j → ℚ := fun r => (u r : ℚ) with hv`. Use `set P : ℚ := ∏ r, ((u r).factorial : ℚ) with hP`. Establish `hP0 : P ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun r _ => by positivity`. Establish `key` using `hV j v`.

Establish `hterm : ∀ p, (if 0 < u p ∧ ∀ q, u q ≠ u p - 1 then hookFactor (Function.update u p (u p - 1)) else 0) = v p * (Matrix.vandermonde (Function.update v p (v p - 1))).det / P`. Introduce `p`. Use `split_ifs with h`. Take `⟨hp, -⟩` from `h`. Establish `hcast : (fun r => ((Function.update u p (u p - 1) r : ℕ) : ℚ)) = Function.update v p (v p - 1)`.

Use function extensionality and compare the values at `r`. Distinguish the cases in `hr : r = p`. Substitute `hr` using the available equality. Simplify using `[hv, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hp.ne')]`. Simplify using `[hr, hv]`.

Establish `hprod : (u p : ℚ) * ∏ r, ((Function.update u p (u p - 1) r).factorial : ℚ) = P`. Rewrite using `[hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ p), ← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Function.update_self, ← mul_assoc, ← Nat.cast_mul, Nat.mul_factorial_pred hp.ne']`. Use `congr 1`. Use `Finset.prod_congr rfl fun r hr => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hr)]`.

Establish `hup : (u p : ℚ) ≠ 0` using `by exact_mod_cast hp.ne'`. Unfold `hookFactor`. Rewrite using `[hcast, ← hprod, mul_div_mul_left _ _ hup]`. Distinguish the cases in `hp : u p = 0`. Simplify using `[hv, hp]`.

Use `push Not at h`. Take `⟨q, hq⟩` from `h (Nat.pos_of_ne_zero hp)`. Establish `hqp : q ≠ p`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers.

Establish `hdet : (Matrix.vandermonde (Function.update v p (v p - 1))).det = 0`. Use `Matrix.det_vandermonde_eq_zero_iff.mpr ⟨q, p, ?_, hqp⟩` and prove the remaining obligations. Rewrite using `[Function.update_of_ne hqp, Function.update_self]`. Simplify using `only [hv, hq]`. Rewrite using `[Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hp), Nat.cast_one]`.

Rewrite using `[hdet, mul_zero, zero_div]`. Rewrite using `[Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_div, key]`. Unfold `hookFactor`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem HookFactorBranch.proof (hV : VandermondeBranch.Statement) : HookFactorBranch.Statement := by
  intro j u
  set v : Fin j → ℚ := fun r => (u r : ℚ) with hv
  set P : ℚ := ∏ r, ((u r).factorial : ℚ) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r _ => by positivity
  have key := hV j v
  have hterm : ∀ p, (if 0 < u p ∧ ∀ q, u q ≠ u p - 1 then hookFactor (Function.update u p (u p - 1))
      else 0) = v p * (Matrix.vandermonde (Function.update v p (v p - 1))).det / P := by
    intro p
    split_ifs with h
    · obtain ⟨hp, -⟩ := h
      have hcast : (fun r => ((Function.update u p (u p - 1) r : ℕ) : ℚ)) =
          Function.update v p (v p - 1) := by
        funext r
        by_cases hr : r = p
        · subst hr
          simp [hv, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hp.ne')]
        · simp [hr, hv]
      have hprod : (u p : ℚ) * ∏ r, ((Function.update u p (u p - 1) r).factorial : ℚ) = P := by
        rw [hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ p),
          ← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Function.update_self, ← mul_assoc,
          ← Nat.cast_mul, Nat.mul_factorial_pred hp.ne']
        congr 1
        refine Finset.prod_congr rfl fun r hr => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hr)]
      have hup : (u p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
      unfold hookFactor
      rw [hcast, ← hprod, mul_div_mul_left _ _ hup]
    · by_cases hp : u p = 0
      · simp [hv, hp]
      · push Not at h
        obtain ⟨q, hq⟩ := h (Nat.pos_of_ne_zero hp)
        have hqp : q ≠ p := by
          rintro rfl
          omega
        have hdet : (Matrix.vandermonde (Function.update v p (v p - 1))).det = 0 := by
          refine Matrix.det_vandermonde_eq_zero_iff.mpr ⟨q, p, ?_, hqp⟩
          rw [Function.update_of_ne hqp, Function.update_self]
          simp only [hv, hq]
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hp), Nat.cast_one]
        rw [hdet, mul_zero, zero_div]
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_div, key]
  unfold hookFactor
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
