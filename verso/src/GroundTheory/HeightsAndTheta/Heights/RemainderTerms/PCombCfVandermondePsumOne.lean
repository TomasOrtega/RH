import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

/- English proof (translation)
Introduce `m n l hl`. Establish `hA : alternantPsum m (List.replicate n 1) = alt (stair m) * psum (Fin m) ℚ 1 ^ n`. Simplify using `only [alternantPsum, List.map_replicate, List.prod_replicate, vandermondeOf_X_eq_alt]`. Establish `hterm : ∀ σ : Perm (Fin m), cf l (monomial (ex (stair m ∘ σ.symm)) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) = ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) * ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ)`. Introduce `σ`.

Rewrite using `[h1]`. Establish `hsum : ∑ i, l i = ∑ i, (stair m ∘ σ.symm) i + n`. Rewrite using `[hl, Function.comp_def, Equiv.sum_comp σ.symm (stair m)]`. Distinguish the cases in `hle : ∀ i, (stair m ∘ σ.symm) i ≤ l i`. Rewrite using `[if_pos ⟨hle, hsum⟩]`.

Establish `hd : ∀ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) = ((l i).factorial : ℚ) / ((l i - stair m (σ.symm i)).factorial : ℚ)`. Introduce `i`. Rewrite using `[eq_div_iff (by positivity), mul_comm]`. Conclude with `Nat.factorial_mul_descFactorial (hle i)` after adjusting the coercions. Simplify using `only [hd, Finset.prod_div_distrib, Function.comp_apply]`.

Establish `hp : (∏ i, ((l i).factorial : ℚ)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i _ => by positivity`. Establish `hq : (∏ i, ((l i - stair m (σ.symm i)).factorial : ℚ)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i _ => by positivity`. Clear the denominators using the available nonvanishing facts. Rewrite `hle` using `[if_neg (fun h => hle h.1)] push Not`. Take `⟨i, hi⟩` from `hle`.

Simplify using `only [Function.comp_apply] at hi`. Establish `h0 : ∏ j, ((l j).descFactorial (stair m (σ.symm j)) : ℚ) = 0` using `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi])`. Rewrite using `[h0, mul_zero]`. Establish `hdet : ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℚ) * ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) = vandermondeOf (fun i => (l i : ℚ))`. Rewrite using `[← h2 m l, Matrix.det_apply]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, zsmul_eq_mul, ← Equiv.prod_comp σ]`. Simplify using the standard rewrite rules. Rewrite using `[hA, alt_eq_sum, Finset.sum_mul, cf_sum]`. Repeatedly rewrite using `[smul_mul_assoc, cf_zsmul, hterm]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring`. Use `_ = _ := by rw [hdet]; ring`.
-/
theorem CombCfVandermondePsumOne.proof (h1 : CombCfMonomialPsumOne.Statement)
    (h2 : CombDetDescFactorial.Statement) : CombCfVandermondePsumOne.Statement := by
  intro m n l hl
  have hA : alternantPsum m (List.replicate n 1) = alt (stair m) * psum (Fin m) ℚ 1 ^ n := by
    simp only [alternantPsum, List.map_replicate, List.prod_replicate, vandermondeOf_X_eq_alt]
  have hterm : ∀ σ : Perm (Fin m),
      cf l (monomial (ex (stair m ∘ σ.symm)) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) =
        ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) *
          ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
    intro σ
    rw [h1]
    have hsum : ∑ i, l i = ∑ i, (stair m ∘ σ.symm) i + n := by
      rw [hl, Function.comp_def, Equiv.sum_comp σ.symm (stair m)]
    by_cases hle : ∀ i, (stair m ∘ σ.symm) i ≤ l i
    · rw [if_pos ⟨hle, hsum⟩]
      have hd : ∀ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) =
          ((l i).factorial : ℚ) / ((l i - stair m (σ.symm i)).factorial : ℚ) := by
        intro i
        rw [eq_div_iff (by positivity), mul_comm]
        exact_mod_cast Nat.factorial_mul_descFactorial (hle i)
      simp only [hd, Finset.prod_div_distrib, Function.comp_apply]
      have hp : (∏ i, ((l i).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      have hq : (∏ i, ((l i - stair m (σ.symm i)).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      field_simp
    · rw [if_neg (fun h => hle h.1)]
      push Not at hle
      obtain ⟨i, hi⟩ := hle
      simp only [Function.comp_apply] at hi
      have h0 : ∏ j, ((l j).descFactorial (stair m (σ.symm j)) : ℚ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi])
      rw [h0, mul_zero]
  have hdet : ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℚ) *
      ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) = vandermondeOf (fun i => (l i : ℚ)) := by
    rw [← h2 m l, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, ← Equiv.prod_comp σ]
    simp
  rw [hA, alt_eq_sum, Finset.sum_mul, cf_sum]
  simp_rw [smul_mul_assoc, cf_zsmul, hterm]
  calc _ = ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) * ∑ σ : Perm (Fin m),
        ((Perm.sign σ : ℤ) : ℚ) * ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [hdet]; ring

end

end GroundTheory.Heights₂.Heights.RestTerms
