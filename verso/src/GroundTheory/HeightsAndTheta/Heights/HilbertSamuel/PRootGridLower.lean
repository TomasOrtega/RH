import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootGridLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Finset

/- English proof (translation)
Establish `hω0 : ω ≠ 0` using `hω.ne_zero hM.ne'`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun t => (ω ^ a * (ω ^ b)⁻¹) ^ t)]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Simplify using `[mul_inv_cancel₀ (pow_ne_zero _ hω0)]`.

Establish `hz : ω ^ a * (ω ^ b)⁻¹ ≠ 1`. Introduce `h`. Apply `hab` to reduce the goal to its premises. Apply `hω.pow_inj ha hb` to reduce the goal to its premises. Use `congrArg (· * ω ^ b) h` as an intermediate fact.

Simplify `this` using `[mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hω0)]`. Rewrite using `[geom_sum_eq hz]`. Establish `h1 : (ω ^ a * (ω ^ b)⁻¹) ^ M = 1`. Rewrite using `[mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul, hω.pow_eq_one]`. Simplify using the standard rewrite rules.

Simplify using `[h1]`.
-/
theorem RootGridLower.sum_fin_pow {M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    {a b : ℕ} (ha : a < M) (hb : b < M) :
    ∑ t : Fin M, (ω ^ a * (ω ^ b)⁻¹) ^ (t : ℕ) = if a = b then (M : ℂ) else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero hM.ne'
  rw [Fin.sum_univ_eq_sum_range (fun t => (ω ^ a * (ω ^ b)⁻¹) ^ t)]
  split_ifs with hab
  · subst hab
    simp [mul_inv_cancel₀ (pow_ne_zero _ hω0)]
  · have hz : ω ^ a * (ω ^ b)⁻¹ ≠ 1 := by
      intro h
      apply hab
      apply hω.pow_inj ha hb
      have := congrArg (· * ω ^ b) h
      simpa [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hω0)] using this
    rw [geom_sum_eq hz]
    have h1 : (ω ^ a * (ω ^ b)⁻¹) ^ M = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    simp [h1]

/- English proof (translation)
Repeatedly rewrite using `[eval_map, eval₂_eq', Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `key : ∀ d ∈ Q.support, ∑ k : Fin e → Fin M, (Int.castRingHom ℂ) (Q.coeff d) * (∏ i, (ω ^ (k i : ℕ)) ^ d i) * ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) = ((Q.coeff d : ℤ) : ℂ) * if d = j then (M : ℂ) ^ e else 0`. Introduce `d hd`. Establish `hdM : ∀ i, d i < M` using `fun i => lt_of_le_of_lt (monomial_le_degreeOf i hd) (hdeg i)`.

Establish `hprod : ∀ k : Fin e → Fin M, (∏ i, (ω ^ (k i : ℕ)) ^ d i) * ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) = ∏ i, (ω ^ d i * (ω ^ j i)⁻¹) ^ (k i : ℕ)`. Introduce `k`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, ← pow_mul, ← pow_mul, mul_comm (k i : ℕ)]`.

Repeatedly rewrite using `[mul_assoc, hprod, ← Finset.mul_sum]`. Use `congr 1`. Rewrite using `[← Fintype.prod_sum (fun i (t : Fin M) => (ω ^ d i * (ω ^ j i)⁻¹) ^ (t : ℕ))]`. Repeatedly rewrite using `[RootGridLower.sum_fin_pow hM hω (hdM _) (hj _)]`. Use `split_ifs with hdj`.

Substitute `hdj` using the available equality. Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, d i ≠ j i := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hdj (Finsupp.ext h)`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)`. Rewrite using `[Finset.sum_congr rfl key]`. Repeatedly rewrite using `[mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq']`.

Use `split_ifs with hjs`. Simplify using `[mul_comm]`. Rewrite using `[MvPolynomial.notMem_support_iff.mp hjs]`. Simplify using the standard rewrite rules.
-/
theorem RootGridLower.average {e M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    (Q : MvPolynomial (Fin e) ℤ) (hdeg : ∀ i, Q.degreeOf i < M) (j : Fin e →₀ ℕ)
    (hj : ∀ i, j i < M) :
    ∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) = (M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ) := by
  classical
  simp_rw [eval_map, eval₂_eq', Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ d ∈ Q.support, ∑ k : Fin e → Fin M,
      (Int.castRingHom ℂ) (Q.coeff d) * (∏ i, (ω ^ (k i : ℕ)) ^ d i) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) =
      ((Q.coeff d : ℤ) : ℂ) * if d = j then (M : ℂ) ^ e else 0 := by
    intro d hd
    have hdM : ∀ i, d i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hd) (hdeg i)
    have hprod : ∀ k : Fin e → Fin M, (∏ i, (ω ^ (k i : ℕ)) ^ d i) * ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)
        = ∏ i, (ω ^ d i * (ω ^ j i)⁻¹) ^ (k i : ℕ) := by
      intro k
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k i : ℕ)]
    simp_rw [mul_assoc, hprod, ← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun i (t : Fin M) => (ω ^ d i * (ω ^ j i)⁻¹) ^ (t : ℕ))]
    simp_rw [RootGridLower.sum_fin_pow hM hω (hdM _) (hj _)]
    split_ifs with hdj
    · subst hdj; simp
    · obtain ⟨i, hi⟩ : ∃ i, d i ≠ j i := by
        by_contra h
        push Not at h
        exact hdj (Finsupp.ext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [Finset.sum_congr rfl key]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hjs
  · simp [mul_comm]
  · rw [MvPolynomial.notMem_support_iff.mp hjs]; simp

/- English proof (translation)
Establish `hω` using `Complex.isPrimitiveRoot_exp M hM.ne'`. Use `set ω := Complex.exp (2 * Real.pi * Complex.I / M)`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : Q.support.Nonempty := by`. Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]`. Conclude with `hQ`.

Establish `hjM : ∀ i, j i < M` using `fun i => lt_of_le_of_lt (monomial_le_degreeOf i hj) (hdeg i)`. Establish `hc : (1 : ℝ) ≤ ‖((Q.coeff j : ℤ) : ℂ)‖`. Rewrite using `[Complex.norm_intCast]`. Conclude with `Int.one_le_abs (MvPolynomial.mem_support_iff.mp hj)` after adjusting the coercions. Establish `hω1 : ‖ω‖ = 1` using `hω.norm'_eq_one hM.ne'`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hlt : ∀ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ < 1`. Introduce `k`. Use `hne _ fun i => ?_` and prove the remaining obligations.

Rewrite using `[← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]`. Establish `hne' : (Finset.univ : Finset (Fin e → Fin M)).Nonempty` using `⟨fun i => ⟨j i, hjM i⟩, Finset.mem_univ _⟩`. Establish `hupper : ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ < (M : ℝ) ^ e`. Rewrite using `[← RootGridLower.average hM hω Q hdeg j hjM]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[norm_prod, hω1]`. Use `_ < ∑ _k : Fin e → Fin M, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty hne' fun k _ => hlt k`. Use `_ = (M : ℝ) ^ e := by simp`. Establish `hlower : (M : ℝ) ^ e ≤ ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖`.

Rewrite using `[norm_mul, norm_pow, Complex.norm_natCast]`. Conclude with `le_mul_of_one_le_right (by positivity) hc`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem RootGridLower.of_pos {e M : ℕ} (hM : 0 < M) (Q : MvPolynomial (Fin e) ℤ) (hQ : Q ≠ 0)
    (hdeg : ∀ i, Q.degreeOf i < M) :
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ M = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖ := by
  classical
  have hω := Complex.isPrimitiveRoot_exp M hM.ne'
  set ω := Complex.exp (2 * Real.pi * Complex.I / M)
  obtain ⟨j, hj⟩ : Q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hQ
  have hjM : ∀ i, j i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hj) (hdeg i)
  have hc : (1 : ℝ) ≤ ‖((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (MvPolynomial.mem_support_iff.mp hj)
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one hM.ne'
  by_contra hne
  push Not at hne
  have hlt : ∀ k : Fin e → Fin M,
      ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ < 1 := by
    intro k
    refine hne _ fun i => ?_
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hne' : (Finset.univ : Finset (Fin e → Fin M)).Nonempty :=
    ⟨fun i => ⟨j i, hjM i⟩, Finset.mem_univ _⟩
  have hupper : ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ < (M : ℝ) ^ e := by
    rw [← RootGridLower.average hM hω Q hdeg j hjM]
    calc ‖∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖
        ≤ ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖ := norm_sum_le _ _
      _ = ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [norm_prod, hω1]
      _ < ∑ _k : Fin e → Fin M, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty hne' fun k _ => hlt k
      _ = (M : ℝ) ^ e := by simp
  have hlower : (M : ℝ) ^ e ≤ ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact le_mul_of_one_le_right (by positivity) hc
  linarith

/- English proof (translation)
Introduce `e m Q hQ hdeg`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Take `⟨ζ, -, hζ⟩` from `RootGridLower.of_pos Nat.one_pos Q hQ (fun i => lt_trans (hdeg i) Nat.one_pos)`. Conclude with `⟨ζ, fun i => pow_zero _, hζ⟩`. Conclude with `RootGridLower.of_pos hm Q hQ hdeg`.
-/
theorem RootGridLower.proof : RootGridLower.Statement := by
  intro e m Q hQ hdeg
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨ζ, -, hζ⟩ := RootGridLower.of_pos Nat.one_pos Q hQ
      (fun i => lt_trans (hdeg i) Nat.one_pos)
    exact ⟨ζ, fun i => pow_zero _, hζ⟩
  · exact RootGridLower.of_pos hm Q hQ hdeg

end GroundTheory.Heights₂.Heights.HilbertSamuel
