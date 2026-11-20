import Mathlib
import Formalism.PeriodIntegrals.QuadDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDifference.QuadDiffOf

noncomputable section

namespace PI.QD

open NumberField Polynomial

/- English proof (translation)
Unfold `Arith`. Introduce `d x y hsq hd4 ⟨u, hu⟩ ⟨N, hN⟩`. Take `⟨M, hM⟩ : ∃ M : ℤ, (d : ℚ) * (2 * y) ^ 2 = M` from `⟨4 * N - u ^ 2, by`. Use `push_cast`. Take the linear combination `4 * hN - (2 * x + (u : ℚ)) * hu⟩`.

Take `⟨w, hw⟩ : ∃ w : ℚ, w = 2 * y` from `⟨_, rfl⟩`. Rewrite `hM` using `[← hw]`. Establish `h2 : w * w.den = w.num` using `Rat.mul_den_eq_num w`. Establish `h3 : ((d * w.num ^ 2 : ℤ) : ℚ) = ((M * (w.den : ℤ) ^ 2 : ℤ) : ℚ)`. Use `push_cast`.

Rewrite using `[← h2]`. Take the linear combination `(w.den : ℚ) ^ 2 * hM`. Establish `key : (d : ℤ) * w.num ^ 2 = M * (w.den : ℤ) ^ 2` using `by exact_mod_cast h3`. Establish `hcop : IsCoprime ((w.den : ℤ) ^ 2) (w.num ^ 2)` using `(Int.isCoprime_iff_gcd_eq_one.mpr (show Int.gcd w.num (w.den : ℤ) = 1 from w.reduced)).symm.pow`. Establish `hdvd : (w.den : ℤ) ^ 2 ∣ (d : ℤ)`.

Apply `hcop.dvd_of_dvd_mul_right` to reduce the goal to its premises. Conclude with `⟨M, by rw [key]; ring⟩`. Establish `hdvd' : w.den * w.den ∣ d`. Rewrite using `[← pow_two]`. Conclude with `hdvd` after adjusting the coercions.

Establish `hden : w.den = 1` using `Nat.isUnit_iff.mp (hsq _ hdvd')`. Rewrite `h2` using `[hden, Nat.cast_one, mul_one]`. Take `⟨v, hv⟩ : ∃ v : ℤ, v = w.num` from `⟨_, rfl⟩`. Rewrite `h2`, `key` using `[← hv]`. Rewrite `key` using `[hden]`.

Establish `hE : u ^ 2 + (d : ℤ) * v ^ 2 = 4 * N`. Establish `h4 : ((u ^ 2 + (d : ℤ) * v ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ)`. Use `push_cast`. Rewrite using `[← h2, hw]`. Take the linear combination `4 * hN - (2 * x + (u : ℚ)) * hu`.

Conclude with `h4` after adjusting the coercions. Take `⟨t, ht⟩ : ∃ t : ℤ, (d : ℤ) = 4 * t + 3` from `⟨((d / 4 : ℕ) : ℤ), by omega⟩`. Rewrite `hE` using `[ht]`. Establish `hpar : ∃ a : ℤ, u - v = 2 * a`. Apply the tactic sequence `rcases Int.even_or_odd' u with ⟨k, hk | hk⟩ <;> rcases Int.even_or_odd' v with ⟨m, hm | hm⟩ <;>`.

Apply the tactic sequence `subst hk <;> subst hm`. Conclude with `⟨k - m, by ring⟩`. It suffices to derive a contradiction. Use `ring_nf at hE`. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Use `ring_nf at hE`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨k - m, by ring⟩`. Take `⟨a, ha⟩` from `hpar`.

Use `⟨a, v, ?_, ?_⟩` and prove the remaining obligations. Establish `ha' : ((u - v : ℤ) : ℚ) = ((2 * a : ℤ) : ℚ)` using `by rw [ha]`. Move the coercions through the operations in `at ha'`. Take the linear combination `hu / 2 + ha' / 2`. Rewrite using `[← h2, hw]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem quadraticDifferenceArith : Arith := by
  unfold Arith
  intro d x y hsq hd4 ⟨u, hu⟩ ⟨N, hN⟩
  obtain ⟨M, hM⟩ : ∃ M : ℤ, (d : ℚ) * (2 * y) ^ 2 = M := ⟨4 * N - u ^ 2, by
    push_cast
    linear_combination 4 * hN - (2 * x + (u : ℚ)) * hu⟩
  obtain ⟨w, hw⟩ : ∃ w : ℚ, w = 2 * y := ⟨_, rfl⟩
  rw [← hw] at hM
  have h2 : w * w.den = w.num := Rat.mul_den_eq_num w
  have h3 : ((d * w.num ^ 2 : ℤ) : ℚ) = ((M * (w.den : ℤ) ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [← h2]
    linear_combination (w.den : ℚ) ^ 2 * hM
  have key : (d : ℤ) * w.num ^ 2 = M * (w.den : ℤ) ^ 2 := by exact_mod_cast h3
  have hcop : IsCoprime ((w.den : ℤ) ^ 2) (w.num ^ 2) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (show Int.gcd w.num (w.den : ℤ) = 1 from w.reduced)).symm.pow
  have hdvd : (w.den : ℤ) ^ 2 ∣ (d : ℤ) := by
    apply hcop.dvd_of_dvd_mul_right
    exact ⟨M, by rw [key]; ring⟩
  have hdvd' : w.den * w.den ∣ d := by
    rw [← pow_two]
    exact_mod_cast hdvd
  have hden : w.den = 1 := Nat.isUnit_iff.mp (hsq _ hdvd')
  rw [hden, Nat.cast_one, mul_one] at h2
  obtain ⟨v, hv⟩ : ∃ v : ℤ, v = w.num := ⟨_, rfl⟩
  rw [← hv] at h2 key
  rw [hden] at key
  have hE : u ^ 2 + (d : ℤ) * v ^ 2 = 4 * N := by
    have h4 : ((u ^ 2 + (d : ℤ) * v ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [← h2, hw]
      linear_combination 4 * hN - (2 * x + (u : ℚ)) * hu
    exact_mod_cast h4
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (d : ℤ) = 4 * t + 3 := ⟨((d / 4 : ℕ) : ℤ), by omega⟩
  rw [ht] at hE
  have hpar : ∃ a : ℤ, u - v = 2 * a := by
    rcases Int.even_or_odd' u with ⟨k, hk | hk⟩ <;> rcases Int.even_or_odd' v with ⟨m, hm | hm⟩ <;>
      subst hk <;> subst hm
    · exact ⟨k - m, by ring⟩
    · exfalso
      ring_nf at hE
      omega
    · exfalso
      ring_nf at hE
      omega
    · exact ⟨k - m, by ring⟩
  obtain ⟨a, ha⟩ := hpar
  refine ⟨a, v, ?_, ?_⟩
  · have ha' : ((u - v : ℤ) : ℚ) = ((2 * a : ℤ) : ℚ) := by rw [ha]
    push_cast at ha'
    linear_combination hu / 2 + ha' / 2
  · rw [← h2, hw]
    ring

/- English proof (translation)
Introduce `K _ _ d θ hθ htop z`. Establish `hz : z ∈ Algebra.adjoin ℚ {θ}` using `by rw [htop]; trivial`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem w hw`. Rewrite `hw` using `[Set.mem_singleton_iff]`.

Conclude with `⟨0, 1, by rw [hw]; simp⟩`. Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`. Consider the case `add w1 w2 _ _ h1 h2`. Take `⟨x1, y1, e1⟩` from `h1`. Take `⟨x2, y2, e2⟩` from `h2`.

Conclude with `⟨x1 + x2, y1 + y2, by rw [e1, e2]; push_cast; ring⟩`. Consider the case `mul w1 w2 _ _ h1 h2`. Take `⟨x1, y1, e1⟩` from `h1`. Take `⟨x2, y2, e2⟩` from `h2`. Use `⟨x1 * x2 - d * y1 * y2, x1 * y2 + x2 * y1, ?_⟩` and prove the remaining obligations.

Rewrite using `[e1, e2]`. Use `push_cast`. Take the linear combination `(y1 * y2 : K) * hθ`.
-/
theorem quadratic_difference_form : Form := by
  intro K _ _ d θ hθ htop z
  have hz : z ∈ Algebra.adjoin ℚ {θ} := by rw [htop]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    exact ⟨0, 1, by rw [hw]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add w1 w2 _ _ h1 h2 =>
    obtain ⟨x1, y1, e1⟩ := h1
    obtain ⟨x2, y2, e2⟩ := h2
    exact ⟨x1 + x2, y1 + y2, by rw [e1, e2]; push_cast; ring⟩
  | mul w1 w2 _ _ h1 h2 =>
    obtain ⟨x1, y1, e1⟩ := h1
    obtain ⟨x2, y2, e2⟩ := h2
    refine ⟨x1 * x2 - d * y1 * y2, x1 * y2 + x2 * y1, ?_⟩
    rw [e1, e2]; push_cast
    linear_combination (y1 * y2 : K) * hθ

/- English proof (translation)
Unfold `IntCoeffs`. Introduce `K _ _ d θ x y hsq hd4 hθ hint`. Establish `hd : (0 : ℚ) < d`. Establish `: 0 < d` using `by omega`. Conclude with `this` after adjusting the coercions.

Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Establish `h1 : IsIntegral ℤ (algebraMap ℚ K x)`. Rewrite using `[eq_ratCast]`. Simplify using `using hint`.

Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.mp ((isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp h1)`. Rewrite `hn` using `[eq_intCast]`. Substitute `hn` using the available equality. Conclude with `⟨⟨2 * n, by push_cast; ring⟩, ⟨n ^ 2, by push_cast; ring⟩⟩`. Take `⟨p, hp⟩ : ∃ p : Polynomial ℚ, p = X ^ 2 - C (2 * x) * X + C (x ^ 2 + d * y ^ 2)` from `⟨_, rfl⟩`.

Establish `hmonic : p.Monic`. Rewrite using `[hp]`. Use `monicity!`. Establish `hdeg : p.natDegree = 2`. Rewrite using `[hp]`.

Use `compute_degree!`. Establish `haeval : aeval ((x : K) + (y : K) * θ) p = 0`. Rewrite using `[hp]`. Simplify using `only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow, eq_ratCast]`. Use `push_cast`.

Take the linear combination `((y : K)) ^ 2 * hθ`. Establish `hirr : Irreducible p`. Rewrite using `[hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]`. Use `Multiset.eq_zero_of_forall_notMem fun r hr => ?_` and prove the remaining obligations. Rewrite `hr` using `[mem_roots hmonic.ne_zero, IsRoot, hp]`.

Simplify using `only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr`. Establish `hy2 : 0 < y ^ 2` using `by positivity`. Use polynomial arithmetic with `[sq_nonneg (r - x), mul_pos hd hy2]`. Establish `hmin : p = minpoly ℚ ((x : K) + (y : K) * θ)` using `minpoly.eq_of_irreducible_of_monic hirr haeval hmonic`. Establish `hg` using `minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint`.

Establish `hc : ∀ i, p.coeff i = ((minpoly ℤ ((x : K) + (y : K) * θ)).coeff i : ℚ)`. Introduce `i`. Rewrite using `[hmin, hg, Polynomial.coeff_map, eq_intCast]`. Establish `h1 : p.coeff 1 = -(2 * x)`. Rewrite using `[hp]`.

Simplify using the standard rewrite rules. Rewrite using `[← C_pow, ← C_pow, coeff_C, coeff_C]`. Simplify using the standard rewrite rules. Establish `h0 : p.coeff 0 = x ^ 2 + d * y ^ 2`. Rewrite using `[hp]`.

Simplify using the standard rewrite rules. Rewrite using `[← C_pow, ← C_pow, coeff_C, coeff_C]`. Simplify using the standard rewrite rules. Use `⟨⟨-(minpoly ℤ ((x : K) + (y : K) * θ)).coeff 1, ?_⟩, ⟨(minpoly ℤ ((x : K) + (y : K) * θ)).coeff 0, ?_⟩⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[← hc, h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hc, h0]`.
-/
theorem quadratic_intCoeffs : IntCoeffs := by
  unfold IntCoeffs
  intro K _ _ d θ x y hsq hd4 hθ hint
  have hd : (0 : ℚ) < d := by
    have : 0 < d := by omega
    exact_mod_cast this
  by_cases hy : y = 0
  · subst hy
    have h1 : IsIntegral ℤ (algebraMap ℚ K x) := by
      rw [eq_ratCast]
      simpa using hint
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp h1)
    rw [eq_intCast] at hn
    subst hn
    exact ⟨⟨2 * n, by push_cast; ring⟩, ⟨n ^ 2, by push_cast; ring⟩⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℚ, p = X ^ 2 - C (2 * x) * X + C (x ^ 2 + d * y ^ 2) := ⟨_, rfl⟩
  have hmonic : p.Monic := by
    rw [hp]
    monicity!
  have hdeg : p.natDegree = 2 := by
    rw [hp]
    compute_degree!
  have haeval : aeval ((x : K) + (y : K) * θ) p = 0 := by
    rw [hp]
    simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow, eq_ratCast]
    push_cast
    linear_combination ((y : K)) ^ 2 * hθ
  have hirr : Irreducible p := by
    rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
    rw [mem_roots hmonic.ne_zero, IsRoot, hp] at hr
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (r - x), mul_pos hd hy2]
  have hmin : p = minpoly ℚ ((x : K) + (y : K) * θ) := minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  have hg := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hc : ∀ i, p.coeff i = ((minpoly ℤ ((x : K) + (y : K) * θ)).coeff i : ℚ) := by
    intro i
    rw [hmin, hg, Polynomial.coeff_map, eq_intCast]
  have h1 : p.coeff 1 = -(2 * x) := by
    rw [hp]
    simp
    rw [← C_pow, ← C_pow, coeff_C, coeff_C]
    simp
  have h0 : p.coeff 0 = x ^ 2 + d * y ^ 2 := by
    rw [hp]
    simp
    rw [← C_pow, ← C_pow, coeff_C, coeff_C]
    simp
  refine ⟨⟨-(minpoly ℤ ((x : K) + (y : K) * θ)).coeff 1, ?_⟩, ⟨(minpoly ℤ ((x : K) + (y : K) * θ)).coeff 0, ?_⟩⟩
  · push_cast
    rw [← hc, h1]
    ring
  · rw [← hc, h0]

end PI.QD
