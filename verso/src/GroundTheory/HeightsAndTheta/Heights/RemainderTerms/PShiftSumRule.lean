import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

namespace ShiftSumRule

def flagIntegralLinear (f N : ℕ) : RootRing f N →ₗ[ℚ] ℚ where
  toFun := flagIntegral f N
  map_add' Φ Ψ := by simp only [flagIntegral, coeff_add, add_mul, Finset.sum_add_distrib]
  map_smul' b Φ := by
    simp only [flagIntegral, coeff_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite using `[blockPowerSum, map_sum, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[pderiv_pow, pderiv_X_of_ne (show ((0 : Fin 1), j) ≠ ((0 : Fin 1), i) by simp [hj]), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem pderiv_blockPowerSum (N k : ℕ) (i : Fin N) :
    pderiv ((0 : Fin 1), i) (blockPowerSum 1 N k 0) =
      (k : RootRing 1 N) * X ((0 : Fin 1), i) ^ (k - 1) := by
  classical
  rw [blockPowerSum, map_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [pderiv_pow, pderiv_X_of_ne (show ((0 : Fin 1), j) ≠ ((0 : Fin 1), i) by simp [hj]), mul_zero]
  · simp

/- English proof (translation)
Rewrite using `[eq_sub_iff_add_eq, blockPowerSum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin (r + a) => (i : ℕ) < a)]`. Use `congr 1`. Simplify using `only [smallPowerSum, yRoot, SmallBlock.sign, map_one, one_mul, yIndex]`. Use `Finset.sum_bij (fun j _ => (⟨a + (j : ℕ), by have := j.isLt; omega⟩ : Fin (r + a))) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `j _`.

Simplify using the standard rewrite rules. Introduce `j₁ _ j₂ _ h`. Simplify using `only [Fin.mk.injEq, Nat.add_left_cancel_iff] at h`. Conclude with `Fin.ext h`. Introduce `i hi`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi`. Conclude with `⟨⟨(i : ℕ) - a, by have := i.isLt; omega⟩, Finset.mem_univ _, by ext; simp; omega⟩`. Introduce `j _`. Both sides reduce to the same expression.
-/
theorem sum_first_pow (r a m : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        (X ((0 : Fin 1), i) : RootRing 1 (r + a)) ^ m =
      blockPowerSum 1 (r + a) m 0 - smallPowerSum 1 r a .last m 0 := by
  classical
  rw [eq_sub_iff_add_eq, blockPowerSum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin (r + a) => (i : ℕ) < a)]
  congr 1
  simp only [smallPowerSum, yRoot, SmallBlock.sign, map_one, one_mul, yIndex]
  refine Finset.sum_bij (fun j _ => (⟨a + (j : ℕ), by have := j.isLt; omega⟩ : Fin (r + a)))
    ?_ ?_ ?_ ?_
  · intro j _; simp
  · intro j₁ _ j₂ _ h
    simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at h
    exact Fin.ext h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact ⟨⟨(i : ℕ) - a, by have := i.isLt; omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
  · intro j _; rfl

end ShiftSumRule

open ShiftSumRule in

/- English proof (translation)
Introduce `r a hr ha Q hQ`. Establish `h0 : flagIntegralLinear 1 (r + a) (∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a), pderiv ((0 : Fin 1), i) (restPolynomial 1 r a .last)) = 0` using `(hS 1 r a 0).1.1`. Establish `hnat : ∀ (n : ℕ) (G : RootRing 1 (r + a)), flagIntegralLinear 1 (r + a) ((n : RootRing 1 (r + a)) * G) = n * flagIntegralLinear 1 (r + a) G`. Introduce `n G`. Rewrite using `[show (n : RootRing 1 (r + a)) = C (n : ℚ) from (map_natCast C n).symm, C_mul', map_smul, smul_eq_mul]`.

Establish `hexp : ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a), pderiv ((0 : Fin 1), i) (restPolynomial 1 r a .last) = ∑ k ∈ Icc 1 (r + a), (blockPowerSum 1 (r + a) k 0 * ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a), pderiv ((0 : Fin 1), i) (Q k 0) + (k : R …`. Rewrite using `[hQ]`. Simplify using `only [Fin.sum_univ_one]`. Repeatedly rewrite using `[map_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[← sum_first_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[pderiv_mul, pderiv_blockPowerSum]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h0` using `[hexp, map_sum]`. Establish `hval : ∀ k ∈ Icc 1 (r + a), flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) k 0 * ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a), pderiv ((0 : Fin 1), i) (Q k 0) + (k : RootRing 1 (r + a)) * (blockPowerSum 1 (r + a) (k - 1) 0 - smallPowerSum 1 r a .last (k - …`. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_Icc]`. Rewrite using `[map_add, show flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) k 0 * _) = 0 from h1 1 (r + a) k 0 _ hk.1 hk.2, zero_add, mul_assoc, hnat, sub_mul, map_sub]`.

Rewrite `h0` using `[Finset.sum_congr rfl hval]`. Establish `hI : Icc 1 (r + a) = insert 1 (Icc 2 (r + a))`. Use extensionality with `k`. Simplify using `only [Finset.mem_Icc, Finset.mem_insert]`. Use linear arithmetic over natural numbers and integers.

Rewrite `h0` using `[hI, Finset.sum_insert (by simp)]`. Establish `hk1 : ((1 : ℕ) : ℚ) * (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (1 - 1) 0 * Q 1 0) - flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (1 - 1) 0 * Q 1 0)) = (a : ℚ) * flagIntegral 1 (r + a) (Q 1 0)`. Establish `e1 : blockPowerSum 1 (r + a) 0 0 = ((r + a : ℕ) : RootRing 1 (r + a))`. Simplify using `[blockPowerSum]`. Establish `e2 : smallPowerSum 1 r a .last 0 0 = ((r : ℕ) : RootRing 1 (r + a))`.

Simplify using `[smallPowerSum]`. Rewrite using `[Nat.sub_self, e1, e2, hnat, hnat]`. Express the relevant statement in the definitionally equal form `((1 : ℕ) : ℚ) * (((r + a : ℕ) : ℚ) * flagIntegral 1 (r + a) (Q 1 0) - (r : ℚ) * flagIntegral 1 (r + a) (Q 1 0)) = _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hk2 : ∀ k ∈ Icc 2 (r + a), (k : ℚ) * (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) - flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (k - 1) 0 * Q k 0)) = -restTerm 1 (r + a) Q k 0 (smallPowerSum 1 r a .last (k - 1) 0)`. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_Icc]`. Rewrite using `[show flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) = 0 from h1 1 (r + a) (k - 1) 0 _ (by omega) (by omega), zero_sub, restTerm, mul_neg]`. Both sides reduce to the same expression.

Rewrite `h0` using `[hk1, Finset.sum_congr rfl hk2, Finset.sum_neg_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ShiftSumRule.proof (hS : ShiftTotalValues.Statement)
    (h1 : FlagIntegralKillsPowerSums.Statement) : ShiftSumRule.Statement := by
  classical
  intro r a hr ha Q hQ
  have h0 : flagIntegralLinear 1 (r + a)
      (∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        pderiv ((0 : Fin 1), i) (restPolynomial 1 r a .last)) = 0 :=
    (hS 1 r a 0).1.1
  have hnat : ∀ (n : ℕ) (G : RootRing 1 (r + a)),
      flagIntegralLinear 1 (r + a) ((n : RootRing 1 (r + a)) * G) =
        n * flagIntegralLinear 1 (r + a) G := by
    intro n G
    rw [show (n : RootRing 1 (r + a)) = C (n : ℚ) from (map_natCast C n).symm, C_mul', map_smul,
      smul_eq_mul]
  have hexp : ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        pderiv ((0 : Fin 1), i) (restPolynomial 1 r a .last) =
      ∑ k ∈ Icc 1 (r + a),
        (blockPowerSum 1 (r + a) k 0 *
            ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
              pderiv ((0 : Fin 1), i) (Q k 0) +
          (k : RootRing 1 (r + a)) *
            (blockPowerSum 1 (r + a) (k - 1) 0 - smallPowerSum 1 r a .last (k - 1) 0) *
              Q k 0) := by
    rw [hQ]
    simp only [Fin.sum_univ_one]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← sum_first_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pderiv_mul, pderiv_blockPowerSum]; ring
  rw [hexp, map_sum] at h0
  have hval : ∀ k ∈ Icc 1 (r + a),
      flagIntegralLinear 1 (r + a)
        (blockPowerSum 1 (r + a) k 0 *
            ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
              pderiv ((0 : Fin 1), i) (Q k 0) +
          (k : RootRing 1 (r + a)) *
            (blockPowerSum 1 (r + a) (k - 1) 0 - smallPowerSum 1 r a .last (k - 1) 0) *
              Q k 0) =
        (k : ℚ) * (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) -
          flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (k - 1) 0 * Q k 0)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [map_add, show flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) k 0 * _) = 0 from
      h1 1 (r + a) k 0 _ hk.1 hk.2, zero_add, mul_assoc, hnat, sub_mul, map_sub]
  rw [Finset.sum_congr rfl hval] at h0
  have hI : Icc 1 (r + a) = insert 1 (Icc 2 (r + a)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.sum_insert (by simp)] at h0
  have hk1 : ((1 : ℕ) : ℚ) *
      (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (1 - 1) 0 * Q 1 0) -
        flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (1 - 1) 0 * Q 1 0)) =
      (a : ℚ) * flagIntegral 1 (r + a) (Q 1 0) := by
    have e1 : blockPowerSum 1 (r + a) 0 0 = ((r + a : ℕ) : RootRing 1 (r + a)) := by
      simp [blockPowerSum]
    have e2 : smallPowerSum 1 r a .last 0 0 = ((r : ℕ) : RootRing 1 (r + a)) := by
      simp [smallPowerSum]
    rw [Nat.sub_self, e1, e2, hnat, hnat]
    change ((1 : ℕ) : ℚ) * (((r + a : ℕ) : ℚ) * flagIntegral 1 (r + a) (Q 1 0) -
      (r : ℚ) * flagIntegral 1 (r + a) (Q 1 0)) = _
    push_cast; ring
  have hk2 : ∀ k ∈ Icc 2 (r + a),
      (k : ℚ) * (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) -
          flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (k - 1) 0 * Q k 0)) =
        -restTerm 1 (r + a) Q k 0 (smallPowerSum 1 r a .last (k - 1) 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [show flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) = 0 from
      h1 1 (r + a) (k - 1) 0 _ (by omega) (by omega), zero_sub, restTerm, mul_neg]
    rfl
  rw [hk1, Finset.sum_congr rfl hk2, Finset.sum_neg_distrib] at h0
  linarith

end

end RestTerms

end GroundTheory.Heights₂.Heights
