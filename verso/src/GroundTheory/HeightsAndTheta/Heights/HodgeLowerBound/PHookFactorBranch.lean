import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHookFactorBranch
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVandermondeBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
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
