import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula

open Finset ArithmeticFunction

namespace Formalism.HermitianLattices.GL2PrimeSums

/- English proof (translation)
Take `⟨p, k, hp, hk, rfl⟩` from `(isPrimePow_nat_iff n).1 hn`. Use `⟨p, k, hp, hk, rfl, hp.pow_minFac hk.ne', ?_⟩` and prove the remaining obligations. Unfold `outPart`. Rewrite using `[Nat.primeFactors_prime_pow hk.ne' hp, Finset.filter_singleton]`. Establish `: (p ^ k).factorization p = k`.

Rewrite using `[hp.factorization_pow]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma gl2a5_outPart_primePow (m₀ : ℕ) {n : ℕ} (hn : IsPrimePow n) :
    ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k ∧ n.minFac = p ∧
      outPart m₀ n = if (¬ p ∣ m₀ ∧ Odd k) then p else 1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
  refine ⟨p, k, hp, hk, rfl, hp.pow_minFac hk.ne', ?_⟩
  unfold outPart
  rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.filter_singleton]
  have : (p ^ k).factorization p = k := by
    rw [hp.factorization_pow]; simp
  rw [this]
  split_ifs <;> simp

/- English proof (translation)
Unfold `outPart`. Rewrite using `[h.primeFactors_mul, Finset.filter_union, Finset.prod_union (Finset.disjoint_filter_filter h.disjoint_primeFactors)]`. Use `congr 1`. Apply `Finset.prod_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Apply `Finset.filter_congr` to reduce the goal to its premises.

Introduce `p hp`. Establish `h0 : m'.factorization p = 0`. Apply `Nat.factorization_eq_zero_of_not_dvd` to reduce the goal to its premises. Introduce `hd`. Conclude with `(Finset.disjoint_left.1 h.disjoint_primeFactors hp) (Nat.mem_primeFactors.2 ⟨(Nat.mem_primeFactors.1 hp).1, hd, by`.

Introduce and unpack `rfl`. Use `(Nat.coprime_zero_right m).1 h` as an intermediate fact. Substitute `this` using the available equality. Simplify using `at hp⟩)`. Rewrite using `[Nat.factorization_mul_of_coprime h]`.

Simplify using `[h0]`. Apply `Finset.prod_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `p hp`. Establish `h0 : m.factorization p = 0`.

Apply `Nat.factorization_eq_zero_of_not_dvd` to reduce the goal to its premises. Introduce `hd`. Conclude with `(Finset.disjoint_right.1 h.disjoint_primeFactors hp) (Nat.mem_primeFactors.2 ⟨(Nat.mem_primeFactors.1 hp).1, hd, by`. Introduce and unpack `rfl`. Use `(Nat.coprime_zero_left m').1 h` as an intermediate fact.

Substitute `this` using the available equality. Simplify using `at hp⟩)`. Rewrite using `[Nat.factorization_mul_of_coprime h]`. Simplify using `[h0]`.
-/
lemma gl2a5_outPart_mul (m₀ : ℕ) {m m' : ℕ} (h : Nat.Coprime m m') :
    outPart m₀ (m * m') = outPart m₀ m * outPart m₀ m' := by
  unfold outPart
  rw [h.primeFactors_mul, Finset.filter_union,
    Finset.prod_union (Finset.disjoint_filter_filter h.disjoint_primeFactors)]
  congr 1
  · apply Finset.prod_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro p hp
    have h0 : m'.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact (Finset.disjoint_left.1 h.disjoint_primeFactors hp)
        (Nat.mem_primeFactors.2 ⟨(Nat.mem_primeFactors.1 hp).1, hd, by
          rintro rfl
          have := (Nat.coprime_zero_right m).1 h
          subst this
          simp at hp⟩)
    rw [Nat.factorization_mul_of_coprime h]
    simp [h0]
  · apply Finset.prod_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro p hp
    have h0 : m.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact (Finset.disjoint_right.1 h.disjoint_primeFactors hp)
        (Nat.mem_primeFactors.2 ⟨(Nat.mem_primeFactors.1 hp).1, hd, by
          rintro rfl
          have := (Nat.coprime_zero_left m').1 h
          subst this
          simp at hp⟩)
    rw [Nat.factorization_mul_of_coprime h]
    simp [h0]

/- English proof (translation)
Take `⟨p, k, hp, hk, rfl, hmf, ho⟩` from `gl2a5_outPart_primePow m₀ hn`. Rewrite using `[ho, hmf]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma gl2a5_out_cases (m₀ : ℕ) {n : ℕ} (hn : IsPrimePow n) :
    outPart m₀ n = 1 ∨ outPart m₀ n = n.minFac := by
  obtain ⟨p, k, hp, hk, rfl, hmf, ho⟩ := gl2a5_outPart_primePow m₀ hn
  rw [ho, hmf]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨p, k, hp, hk, rfl, hmf, ho⟩` from `gl2a5_outPart_primePow m₀ hn`. Rewrite using `[hmf]`. Rewrite `h1` using `[ho]`. Distinguish the cases in `hd : p ∣ m₀`. Conclude with `Or.inl hd`.

Use `right`. Distinguish the cases in `hodd : Odd k`. Rewrite `h1` using `[if_pos ⟨hd, hodd⟩]`. Conclude with `absurd h1 hp.one_lt.ne'`. Take `⟨j, hj⟩` from `Nat.not_odd_iff_even.1 hodd`.

Conclude with `⟨p ^ j, by rw [← pow_mul, hj]; congr 1; ring⟩`.
-/
lemma gl2a5_out_one (m₀ : ℕ) {n : ℕ} (hn : IsPrimePow n) (h1 : outPart m₀ n = 1) :
    n.minFac ∣ m₀ ∨ ∃ m, n = m ^ 2 := by
  obtain ⟨p, k, hp, hk, rfl, hmf, ho⟩ := gl2a5_outPart_primePow m₀ hn
  rw [hmf]
  rw [ho] at h1
  by_cases hd : p ∣ m₀
  · exact Or.inl hd
  · right
    by_cases hodd : Odd k
    · rw [if_pos ⟨hd, hodd⟩] at h1
      exact absurd h1 hp.one_lt.ne'
    · obtain ⟨j, hj⟩ := Nat.not_odd_iff_even.1 hodd
      exact ⟨p ^ j, by rw [← pow_mul, hj]; congr 1; ring⟩

/- English proof (translation)
Take `⟨p, k, hp, hk, rfl⟩` from `(isPrimePow_nat_iff n).1 hn`. Take `⟨p', k', hp', hk', rfl⟩` from `(isPrimePow_nat_iff n').1 hn'`. Rewrite `h` using `[hp.pow_minFac hk.ne', hp'.pow_minFac hk'.ne']`. Conclude with `Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hp').2 h)`.
-/
lemma gl2a5_coprime_of_minFac_ne {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (h : n.minFac ≠ n'.minFac) : Nat.Coprime n n' := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
  obtain ⟨p', k', hp', hk', rfl⟩ := (isPrimePow_nat_iff n').1 hn'
  rw [hp.pow_minFac hk.ne', hp'.pow_minFac hk'.ne'] at h
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hp').2 h)

/- English proof (translation)
The claim follows from `|μ| ≤ δ + (if n.minFac = n'.minFac then (1 : ℝ) else 0) + (if outPart m₀ n = 1 ∧ outPart m₀ n' = 1 then (1 : ℝ) else 0) + (if outPart m₀ n = nStar.minFac ∧ outPart m₀ n' = nStar / nStar.minFac then (1 : ℝ) else 0) + (if outPart m₀ n = nStar / nStar.minFac ∧ outPart m₀ n' = nStar. …`.
-/
lemma gl2a5_pointwise (m₀ nStar : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (μ δ : ℝ) (hδ : 0 ≤ δ) (hμ1 : |μ| ≤ 1)
    (hμ : outPart m₀ (n * n') ≠ 1 → outPart m₀ (n * n') ≠ nStar → |μ| ≤ δ) :
    |μ| ≤ δ + (if n.minFac = n'.minFac then (1 : ℝ) else 0)
      + (if outPart m₀ n = 1 ∧ outPart m₀ n' = 1 then (1 : ℝ) else 0)
      + (if outPart m₀ n = nStar.minFac ∧ outPart m₀ n' = nStar / nStar.minFac then (1 : ℝ) else 0)
      + (if outPart m₀ n = nStar / nStar.minFac ∧ outPart m₀ n' = nStar.minFac then (1 : ℝ) else 0) := by
  have i1 : (0 : ℝ) ≤ (if n.minFac = n'.minFac then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have i2 : (0 : ℝ) ≤ (if outPart m₀ n = 1 ∧ outPart m₀ n' = 1 then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have i3 : (0 : ℝ) ≤ (if outPart m₀ n = nStar.minFac ∧ outPart m₀ n' = nStar / nStar.minFac
      then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have i4 : (0 : ℝ) ≤ (if outPart m₀ n = nStar / nStar.minFac ∧ outPart m₀ n' = nStar.minFac
      then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  by_cases h1 : n.minFac = n'.minFac
  · rw [if_pos h1] at i1 ⊢; linarith
  have hmul := gl2a5_outPart_mul m₀ (gl2a5_coprime_of_minFac_ne hn hn' h1)
  by_cases h2 : outPart m₀ (n * n') = 1
  · rw [hmul] at h2
    have h2' : outPart m₀ n = 1 ∧ outPart m₀ n' = 1 :=
      ⟨Nat.eq_one_of_mul_eq_one_right h2, Nat.eq_one_of_mul_eq_one_left h2⟩
    rw [if_pos h2'] at i2 ⊢; linarith
  by_cases h3 : outPart m₀ (n * n') = nStar
  · have hS1 : nStar ≠ 1 := by rw [← h3]; exact h2
    have hr : nStar.minFac.Prime := Nat.minFac_prime hS1
    have hdvd : nStar.minFac ∣ outPart m₀ n * outPart m₀ n' := by
      rw [← hmul, h3]; exact Nat.minFac_dvd _
    have aux : ∀ {k : ℕ}, IsPrimePow k → nStar.minFac ∣ outPart m₀ k →
        outPart m₀ k = nStar.minFac := by
      intro k hk hd
      rcases gl2a5_out_cases m₀ hk with h | h
      · rw [h] at hd; exact absurd (Nat.dvd_one.1 hd) hr.one_lt.ne'
      · rw [h] at hd ⊢
        exact ((Nat.prime_dvd_prime_iff_eq hr (Nat.minFac_prime hk.ne_one)).1 hd).symm
    rcases hr.dvd_mul.1 hdvd with hd | hd
    · have e1 := aux hn hd
      have e0 : nStar = nStar.minFac * outPart m₀ n' := by rw [← e1, ← hmul, h3]
      have e2 : outPart m₀ n' = nStar / nStar.minFac := (Nat.div_eq_of_eq_mul_right hr.pos e0).symm
      have e3 : outPart m₀ n = nStar.minFac ∧ outPart m₀ n' = nStar / nStar.minFac := ⟨e1, e2⟩
      rw [if_pos e3]; linarith
    · have e1 := aux hn' hd
      have e0 : nStar = outPart m₀ n * nStar.minFac := by rw [← e1, ← hmul, h3]
      have e2 : outPart m₀ n = nStar / nStar.minFac := (Nat.div_eq_of_eq_mul_left hr.pos e0).symm
      have e3 : outPart m₀ n = nStar / nStar.minFac ∧ outPart m₀ n' = nStar.minFac := ⟨e2, e1⟩
      rw [if_pos e3]; linarith
  · have := hμ h2 h3
    linarith

/- English proof (translation)
Rewrite using `[Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n' _`.

Apply the tactic sequence `by_cases hA : A n <;> by_cases hB : B n' <;> simp [hA, hB]`.
-/
lemma gl2a5_sum_ind (P : Finset ℕ) (c : ℕ → ℝ) (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B] :
    ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if A n ∧ B n' then (1 : ℝ) else 0) =
      (∑ n ∈ P.filter A, c n) * (∑ n ∈ P.filter B, c n) := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro n' _
  by_cases hA : A n <;> by_cases hB : B n' <;> simp [hA, hB]

/- English proof (translation)
Establish `e1 : δ * (∑ n ∈ P, c n) ^ 2 = ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * δ`. Rewrite using `[sq, Finset.sum_mul_sum, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n' _`. Expand and normalize the polynomial expressions, which then agree. Establish `e2` using `gl2a5_sum_ind P c (fun n => o n = 1) (fun n => o n = 1)`. Establish `e3` using `gl2a5_sum_ind P c (fun n => o n = r) (fun n => o n = r')`.

Establish `e4` using `gl2a5_sum_ind P c (fun n => o n = r') (fun n => o n = r)`. Establish `e5 : 2 * ((∑ n ∈ P.filter (fun n => o n = r), c n) * (∑ n ∈ P.filter (fun n => o n = r'), c n)) = (∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if o n = r ∧ o n' = r' then (1 : ℝ) else 0)) + (∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if o n = r' ∧ o n' = r then (1 : ℝ) else 0))`. Rewrite using `[e3, e4]`. Expand and normalize the polynomial expressions, which then agree. Establish `e6 : (∑ n ∈ P.filter (fun n => o n = 1), c n) ^ 2 = (∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if o n = 1 ∧ o n' = 1 then (1 : ℝ) else 0))`.

Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e6, e5, ← add_assoc]`. Simplify using `only [← Finset.sum_add_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `n hn`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `n' hn'`. Use `mul_le_mul_of_nonneg_left (hpt n hn n' hn') (mul_nonneg (hc n) (hc n'))` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
lemma gl2a5_comb (P : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (o mf : ℕ → ℕ) (μ : ℕ → ℕ → ℝ)
    (δ : ℝ) (r r' : ℕ)
    (hpt : ∀ n ∈ P, ∀ n' ∈ P, |μ n n'| ≤ δ + (if mf n = mf n' then (1 : ℝ) else 0)
      + (if o n = 1 ∧ o n' = 1 then (1 : ℝ) else 0)
      + (if o n = r ∧ o n' = r' then (1 : ℝ) else 0)
      + (if o n = r' ∧ o n' = r then (1 : ℝ) else 0)) :
    ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * |μ n n'| ≤
      δ * (∑ n ∈ P, c n) ^ 2
      + ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if mf n = mf n' then (1 : ℝ) else 0)
      + (∑ n ∈ P.filter (fun n => o n = 1), c n) ^ 2
      + 2 * ((∑ n ∈ P.filter (fun n => o n = r), c n) * (∑ n ∈ P.filter (fun n => o n = r'), c n)) := by
  have e1 : δ * (∑ n ∈ P, c n) ^ 2 = ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * δ := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n' _
    ring
  have e2 := gl2a5_sum_ind P c (fun n => o n = 1) (fun n => o n = 1)
  have e3 := gl2a5_sum_ind P c (fun n => o n = r) (fun n => o n = r')
  have e4 := gl2a5_sum_ind P c (fun n => o n = r') (fun n => o n = r)
  have e5 : 2 * ((∑ n ∈ P.filter (fun n => o n = r), c n) * (∑ n ∈ P.filter (fun n => o n = r'), c n)) =
      (∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if o n = r ∧ o n' = r' then (1 : ℝ) else 0)) +
      (∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if o n = r' ∧ o n' = r then (1 : ℝ) else 0)) := by
    rw [e3, e4]; ring
  have e6 : (∑ n ∈ P.filter (fun n => o n = 1), c n) ^ 2 =
      (∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if o n = 1 ∧ o n' = 1 then (1 : ℝ) else 0)) := by
    rw [e2]; ring
  rw [e1, e6, e5, ← add_assoc]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro n hn
  apply Finset.sum_le_sum; intro n' hn'
  have := mul_le_mul_of_nonneg_left (hpt n hn n' hn') (mul_nonneg (hc n) (hc n'))
  calc _ ≤ _ := this
    _ = _ := by ring

/- English proof (translation)
Establish `key : ((∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ I, ∑ n' ∈ I, a n * (starRingEnd ℂ) (a n') * ((∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ) : ℝ) : ℂ)`. Use `push_cast`. Establish `: ∀ q ∈ PPs, ((‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ : ℂ)) ^ 2 = ∑ n ∈ I, ∑ n' ∈ I, a n * (starRingEnd ℂ) (a n') * ((jacobiSym (n : ℤ) q : ℂ) * (jacobiSym (n' : ℤ) q : ℂ))`. Introduce `q _`. Rewrite using `[← Complex.mul_conj', map_sum, Finset.sum_mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n' _`. Simplify using `only [map_mul, map_intCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`. Rewrite using `[Finset.sum_comm]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n' _`. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `q _`.

Rewrite using `[jacobiSym.mul_left]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hnn : 0 ≤ ∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2` using `Finset.sum_nonneg (fun _ _ => by positivity)`. Establish `hc : ∀ n, 0 ≤ c n` using `fun n => (norm_nonneg _).trans (ha n)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg hnn]`. Use `_ ≤ _ := by`. Rewrite using `[key]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)` and prove the remaining obligations.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul (ha n) (ha n') (norm_nonneg _) (hc n)) (abs_nonneg _)`.
-/
lemma gl2a5_expand (I PPs : Finset ℕ) (a : ℕ → ℂ) (c : ℕ → ℝ) (ha : ∀ n, ‖a n‖ ≤ c n) :
    ∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)| := by
  have key : ((∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ n' ∈ I, a n * (starRingEnd ℂ) (a n') *
        ((∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ) : ℝ) : ℂ) := by
    push_cast
    have : ∀ q ∈ PPs, ((‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ : ℂ)) ^ 2 =
        ∑ n ∈ I, ∑ n' ∈ I, a n * (starRingEnd ℂ) (a n') *
          ((jacobiSym (n : ℤ) q : ℂ) * (jacobiSym (n' : ℤ) q : ℂ)) := by
      intro q _
      rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro n _
      apply Finset.sum_congr rfl; intro n' _
      simp only [map_mul, map_intCast]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro n' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _
    rw [jacobiSym.mul_left]
    push_cast
    ring
  have hnn : 0 ≤ ∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hc : ∀ n, 0 ≤ c n := fun n => (norm_nonneg _).trans (ha n)
  calc ∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2
      = ‖((∑ q ∈ PPs, ‖∑ n ∈ I, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    _ ≤ _ := by
        rw [key]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
        rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (ha n) (ha n') (norm_nonneg _) (hc n)) (abs_nonneg _)

/- English proof (translation)
Establish `hsub : ∀ M : ℕ, ∑ n ∈ Ioc K M, Λ n ≤ 2 * (M : ℝ)`. Introduce `M`. Use `le_trans ?_ (hψ M)` and prove the remaining obligations. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `n hn`.

Simplify using `only [mem_Ioc, mem_Icc] at hn ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `_ _ _`. Conclude with `vonMangoldt_nonneg`. Break down `Nat.lt_or_ge K M with hKM | hKM` into its components or cases.

Establish `key : ∀ M, K + 1 ≤ M → g M * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) ≤ 2 * ((K : ℝ) + 1) * g (K + 1) + 2 * ∑ n ∈ Ioc (K + 1) M, g n - ∑ n ∈ Ioc K M, Λ n * g n`. Introduce `M hM`. Proceed by induction on `M, hM using Nat.le_induction with`. Consider the case `base`. Rewrite using `[Finset.sum_Ioc_succ_top le_rfl, Finset.sum_Ioc_succ_top le_rfl]`.

Simplify using `only [Finset.Ioc_self, Finset.sum_empty]`. Use `push_cast`. Apply `le_of_eq` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ M hM ih`.

Rewrite using `[Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega)]`. Establish `h1` using `hanti M (by omega)`. Establish `h2` using `hsub M`. Establish `h3 : g (M + 1) * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) ≤ g M * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n)` using `mul_le_mul_of_nonneg_right h1 (by linarith)`. Use `push_cast`.

Use polynomial arithmetic with `[h3, ih]`. Establish `h1` using `key M hKM`. Establish `h2 : 0 ≤ g M * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n)` using `mul_nonneg (hnn M hKM) (by linarith [hsub M])`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Finset.Ioc_eq_empty (by omega), Finset.Ioc_eq_empty (by omega)]`.

Simplify using `only [Finset.sum_empty, mul_zero, add_zero]`. Use `hnn (K + 1) (by omega)` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma gl2a5_abel (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (g : ℕ → ℝ) (K : ℕ)
    (hanti : ∀ n, K < n → g (n + 1) ≤ g n) (hnn : ∀ n, K < n → 0 ≤ g n) (M : ℕ) :
    ∑ n ∈ Ioc K M, Λ n * g n ≤ 2 * ((K : ℝ) + 1) * g (K + 1) + 2 * ∑ n ∈ Ioc (K + 1) M, g n := by
  have hsub : ∀ M : ℕ, ∑ n ∈ Ioc K M, Λ n ≤ 2 * (M : ℝ) := by
    intro M
    refine le_trans ?_ (hψ M)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_Ioc, mem_Icc] at hn ⊢
      omega
    · intro _ _ _; exact vonMangoldt_nonneg
  rcases Nat.lt_or_ge K M with hKM | hKM
  · have key : ∀ M, K + 1 ≤ M → g M * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) ≤
        2 * ((K : ℝ) + 1) * g (K + 1) + 2 * ∑ n ∈ Ioc (K + 1) M, g n - ∑ n ∈ Ioc K M, Λ n * g n := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base =>
        rw [Finset.sum_Ioc_succ_top le_rfl, Finset.sum_Ioc_succ_top le_rfl]
        simp only [Finset.Ioc_self, Finset.sum_empty]
        push_cast
        apply le_of_eq; ring
      | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega),
          Finset.sum_Ioc_succ_top (by omega)]
        have h1 := hanti M (by omega)
        have h2 := hsub M
        have h3 : g (M + 1) * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) ≤
            g M * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
        push_cast
        nlinarith [h3, ih]
    have h1 := key M hKM
    have h2 : 0 ≤ g M * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) :=
      mul_nonneg (hnn M hKM) (by linarith [hsub M])
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty, mul_zero, add_zero]
    have := hnn (K + 1) (by omega)
    positivity

/- English proof (translation)
Break down `Nat.lt_or_ge M K with hKM | hKM` into its components or cases. Rewrite using `[Finset.Ioc_eq_empty (by omega)]; simpa using hh K`. Establish `key : ∀ M, K ≤ M → ∑ n ∈ Ioc K M, g n ≤ h K - h M`. Introduce `M hM`. Proceed by induction on `M, hM using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ M hM ih`. Rewrite using `[Finset.sum_Ioc_succ_top hM]`. Combine the linear relations using `[hstep M hM]`. Combine the linear relations using `[key M hKM, hh M]`.
-/
lemma gl2a5_tele (g h : ℕ → ℝ) (K : ℕ) (hstep : ∀ n, K ≤ n → g (n + 1) ≤ h n - h (n + 1))
    (hh : ∀ n, 0 ≤ h n) (M : ℕ) : ∑ n ∈ Ioc K M, g n ≤ h K := by
  rcases Nat.lt_or_ge M K with hKM | hKM
  · rw [Finset.Ioc_eq_empty (by omega)]; simpa using hh K
  · have key : ∀ M, K ≤ M → ∑ n ∈ Ioc K M, g n ≤ h K - h M := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top hM]
        linarith [hstep M hM]
    linarith [key M hKM, hh M]

/- English proof (translation)
Use `gl2a5_tele (fun a => r ^ a) (fun a => 2 * r ^ (a + 1)) a0 (by` as an intermediate fact. Introduce `n _`. Establish `: 0 ≤ r ^ (n + 1)` using `pow_nonneg h0 _`. Simplify using `only [pow_succ] at this ⊢`. Use the proof step `nlinarith) (fun n => by positivity) L`.

Conclude with `this`.
-/
lemma gl2a5_geom (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (a0 L : ℕ) :
    ∑ a ∈ Ioc a0 L, r ^ a ≤ 2 * r ^ (a0 + 1) := by
  have := gl2a5_tele (fun a => r ^ a) (fun a => 2 * r ^ (a + 1)) a0 (by
    intro n _
    have : 0 ≤ r ^ (n + 1) := pow_nonneg h0 _
    simp only [pow_succ] at this ⊢
    nlinarith) (fun n => by positivity) L
  exact this

/- English proof (translation)
Rewrite using `[← Finset.sum_union]`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `n hn`. Simplify using `only [mem_Ioc, mem_Icc, mem_union] at hn ⊢`. Use linear arithmetic over natural numbers and integers.

Introduce `n _ _`. Conclude with `hf n`. Rewrite using `[Finset.disjoint_left]`. Introduce `n hn hn'`. Simplify using `only [mem_Ioc, mem_Icc] at hn hn'`.

Use linear arithmetic over natural numbers and integers.
-/
lemma gl2a5_split (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (K N : ℕ) :
    ∑ n ∈ Icc 1 N, f n ≤ ∑ n ∈ Icc 1 K, f n + ∑ n ∈ Ioc K N, f n := by
  rw [← Finset.sum_union]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_Ioc, mem_Icc, mem_union] at hn ⊢
      omega
    · intro n _ _; exact hf n
  · rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [mem_Ioc, mem_Icc] at hn hn'
    omega

/- English proof (translation)
Apply `gl2a5_tele (fun n => (1 : ℝ) / (n : ℝ) ^ 2) (fun n => 1 / (n : ℝ)) K _ (fun n => by positivity) M` to reduce the goal to its premises. Introduce `n hn`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast (by omega : 0 < n)`. Use `push_cast`. Rewrite using `[div_sub_div _ _ hn0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
lemma gl2a5_inv_sq_tail (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ n ∈ Ioc K M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  apply gl2a5_tele (fun n => (1 : ℝ) / (n : ℝ) ^ 2) (fun n => 1 / (n : ℝ)) K _ (fun n => by positivity) M
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  push_cast
  rw [div_sub_div _ _ hn0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/- English proof (translation)
Apply `gl2a5_tele (fun n => Real.log n / (n : ℝ) ^ 2) (fun n => (Real.log n + 2) / (n : ℝ)) K _ (fun n => by` to reduce the goal to its premises. Establish `: 0 ≤ Real.log n` using `Real.log_natCast_nonneg n`. Use the proof step `positivity) M`. Introduce `n hn`. Establish `ht : (1 : ℝ) ≤ n` using `by exact_mod_cast (by omega : 1 ≤ n)`.

Establish `ht0 : (0 : ℝ) < n` using `by linarith`. Use `push_cast`. Use `set t : ℝ := (n : ℝ) with htdef`. Establish `hL : 0 ≤ Real.log (t + 1)` using `Real.log_nonneg (by linarith)`. Establish `hl : Real.log (t + 1) - 1 / t ≤ Real.log t`.

Establish `h1 : Real.log ((t + 1) / t) ≤ (t + 1) / t - 1` using `Real.log_le_sub_one_of_pos (by positivity)`. Rewrite `h1` using `[Real.log_div (by positivity) ht0.ne']`. Establish `h2 : (t + 1) / t - 1 = 1 / t` using `by field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set L := Real.log (t + 1)`.

Use `set l := Real.log t`. Establish `hlt : L * t - 1 ≤ l * t`. Use `mul_le_mul_of_nonneg_right hl ht0.le` as an intermediate fact. Establish `e : (L - 1 / t) * t = L * t - 1` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : (l + 2) / t - (L + 2) / (t + 1) - L / (t + 1) ^ 2 = ((l * t + 2 * t) * (t + 1) ^ 2 - (L + 2) * t ^ 2 * (t + 1) - L * t ^ 2) / (t ^ 2 * (t + 1) ^ 2)`. Clear the denominators using the available nonvanishing facts. Establish `hnum : 0 ≤ (l * t + 2 * t) * (t + 1) ^ 2 - (L + 2) * t ^ 2 * (t + 1) - L * t ^ 2`. Establish `h1 : (L * t - 1 + 2 * t) * (t + 1) ^ 2 ≤ (l * t + 2 * t) * (t + 1) ^ 2` using `mul_le_mul_of_nonneg_right (by linarith) (by positivity)`. Establish `h2 : 0 ≤ L * t` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `: 0 ≤ (l + 2) / t - (L + 2) / (t + 1) - L / (t + 1) ^ 2`. Rewrite using `[e]`. Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma gl2a5_log_sq_tail (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ n ∈ Ioc K M, Real.log n / (n : ℝ) ^ 2 ≤ (Real.log K + 2) / (K : ℝ) := by
  apply gl2a5_tele (fun n => Real.log n / (n : ℝ) ^ 2) (fun n => (Real.log n + 2) / (n : ℝ)) K _
    (fun n => by
      have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      positivity) M
  intro n hn
  have ht : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have ht0 : (0 : ℝ) < n := by linarith
  push_cast
  set t : ℝ := (n : ℝ) with htdef
  have hL : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have hl : Real.log (t + 1) - 1 / t ≤ Real.log t := by
    have h1 : Real.log ((t + 1) / t) ≤ (t + 1) / t - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) ht0.ne'] at h1
    have h2 : (t + 1) / t - 1 = 1 / t := by field_simp; ring
    linarith
  set L := Real.log (t + 1)
  set l := Real.log t
  have hlt : L * t - 1 ≤ l * t := by
    have := mul_le_mul_of_nonneg_right hl ht0.le
    have e : (L - 1 / t) * t = L * t - 1 := by field_simp
    linarith
  have e : (l + 2) / t - (L + 2) / (t + 1) - L / (t + 1) ^ 2 =
      ((l * t + 2 * t) * (t + 1) ^ 2 - (L + 2) * t ^ 2 * (t + 1) - L * t ^ 2) / (t ^ 2 * (t + 1) ^ 2) := by
    field_simp
  have hnum : 0 ≤ (l * t + 2 * t) * (t + 1) ^ 2 - (L + 2) * t ^ 2 * (t + 1) - L * t ^ 2 := by
    have h1 : (L * t - 1 + 2 * t) * (t + 1) ^ 2 ≤ (l * t + 2 * t) * (t + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : 0 ≤ L * t := by positivity
    nlinarith
  have : 0 ≤ (l + 2) / t - (L + 2) / (t + 1) - L / (t + 1) ^ 2 := by
    rw [e]; positivity
  linarith

/- English proof (translation)
Unfold `cn`. Conclude with `mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (by positivity))`.
-/
lemma gl2a5_cn_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cn x n := by
  unfold cn
  exact mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (by positivity))

/- English proof (translation)
Unfold `cn`. Conclude with `mul_le_of_le_one_right vonMangoldt_nonneg (min_le_left _ _)`.
-/
lemma gl2a5_cn_le (x : ℝ) (n : ℕ) : cn x n ≤ Λ n := by
  unfold cn
  exact mul_le_of_le_one_right vonMangoldt_nonneg (min_le_left _ _)

/- English proof (translation)
Unfold `cn`. Rewrite using `[vonMangoldt_eq_zero_iff.2 hn, zero_mul]`.
-/
lemma gl2a5_cn_zero (x : ℝ) {n : ℕ} (hn : ¬ IsPrimePow n) : cn x n = 0 := by
  unfold cn
  rw [vonMangoldt_eq_zero_iff.2 hn, zero_mul]

def primesLeFinset (N : ℕ) : Finset ℕ := (Icc 1 N).filter IsPrimePow

noncomputable def primeTermWeight (x : ℝ) (N p : ℕ) : ℝ := ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p), cn x n

/- English proof (translation)
Distinguish the cases in `hp : p.Prime`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `n hn`. Simplify using `only [primesLeFinset, mem_filter, mem_Icc] at hn`.

Take `⟨⟨⟨h1, hN⟩, hpp⟩, hmf⟩` from `hn`. Establish `e` using `hpp.minFac_pow_factorization_eq`. Rewrite `e` using `[hmf]`. Rewrite using `[mem_image]`. Use `⟨n.factorization p, ?_, e⟩` and prove the remaining obligations.

Rewrite using `[mem_Icc]`. Prove the components needed by the constructor for the conclusion. Break down `Nat.eq_zero_or_pos (n.factorization p) with h0 | h0` into its components or cases. Rewrite `e` using `[h0, pow_zero]`. Conclude with `absurd e.symm hpp.ne_one`.

Conclude with `h0`. Establish `: n.factorization p < p ^ n.factorization p` using `Nat.lt_pow_self hp.one_lt`. Use linear arithmetic over natural numbers and integers. Introduce `n _ _`. Conclude with `hf n`.

Use `_ = ∑ a ∈ Icc 1 N, f (p ^ a) := by`. Apply `Finset.sum_image` to reduce the goal to its premises. Introduce `a _ b _ hab`. Conclude with `Nat.pow_right_injective hp.two_le hab`. Establish `: (primesLeFinset N).filter (fun n => n.minFac = p) = ∅`.

Apply `Finset.filter_eq_empty_iff.2` to reduce the goal to its premises. Introduce `n hn hmf`. Simplify using `only [primesLeFinset, mem_filter] at hn`. Conclude with `hp (hmf ▸ Nat.minFac_prime hn.2.ne_one)`. Rewrite using `[this, Finset.sum_empty]`.

Conclude with `Finset.sum_nonneg (fun _ _ => hf _)`.
-/
lemma gl2a5_fiber_le (N p : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p), f n ≤ ∑ a ∈ Icc 1 N, f (p ^ a) := by
  by_cases hp : p.Prime
  · calc ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p), f n
        ≤ ∑ n ∈ (Icc 1 N).image (fun a => p ^ a), f n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [primesLeFinset, mem_filter, mem_Icc] at hn
            obtain ⟨⟨⟨h1, hN⟩, hpp⟩, hmf⟩ := hn
            have e := hpp.minFac_pow_factorization_eq
            rw [hmf] at e
            rw [mem_image]
            refine ⟨n.factorization p, ?_, e⟩
            rw [mem_Icc]
            constructor
            · rcases Nat.eq_zero_or_pos (n.factorization p) with h0 | h0
              · rw [h0, pow_zero] at e
                exact absurd e.symm hpp.ne_one
              · exact h0
            · have : n.factorization p < p ^ n.factorization p := Nat.lt_pow_self hp.one_lt
              omega
          · intro n _ _; exact hf n
      _ = ∑ a ∈ Icc 1 N, f (p ^ a) := by
          apply Finset.sum_image
          intro a _ b _ hab
          exact Nat.pow_right_injective hp.two_le hab
  · have : (primesLeFinset N).filter (fun n => n.minFac = p) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro n hn hmf
      simp only [primesLeFinset, mem_filter] at hn
      exact hp (hmf ▸ Nat.minFac_prime hn.2.ne_one)
    rw [this, Finset.sum_empty]
    exact Finset.sum_nonneg (fun _ _ => hf _)

/- English proof (translation)
The claim follows from `Finset.sum_nonneg (fun _ _ => gl2a5_cn_nonneg hx _)`.
-/
lemma gl2a5s_nonneg {x : ℝ} (hx : 0 ≤ x) (N p : ℕ) : 0 ≤ primeTermWeight x N p :=
  Finset.sum_nonneg (fun _ _ => gl2a5_cn_nonneg hx _)

/- English proof (translation)
Unfold `primeTermWeight`. Establish `: (primesLeFinset N).filter (fun n => n.minFac = p) = ∅`. Apply `Finset.filter_eq_empty_iff.2` to reduce the goal to its premises. Introduce `n hn hmf`. Simplify using `only [primesLeFinset, mem_filter] at hn`.

Conclude with `hp (hmf ▸ Nat.minFac_prime hn.2.ne_one)`. Rewrite using `[this, Finset.sum_empty]`.
-/
lemma gl2a5s_not_prime (x : ℝ) (N : ℕ) {p : ℕ} (hp : ¬ p.Prime) : primeTermWeight x N p = 0 := by
  unfold primeTermWeight
  have : (primesLeFinset N).filter (fun n => n.minFac = p) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro n hn hmf
    simp only [primesLeFinset, mem_filter] at hn
    exact hp (hmf ▸ Nat.minFac_prime hn.2.ne_one)
  rw [this, Finset.sum_empty]

/- English proof (translation)
Establish `hlog : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hcn : ∀ a ∈ Icc 1 N, cn x (p ^ a) = Real.log p * min 1 (x / (p : ℝ) ^ a)`. Introduce `a ha`.

Rewrite `ha` using `[mem_Icc]`. Unfold `cn`. Rewrite using `[vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]`. Use `push_cast`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation. Apply `add_le_add` to reduce the goal to its premises. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `a _`. Conclude with `mul_le_of_le_one_right hlog (min_le_left _ _)`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[mul_assoc]`. Apply `mul_le_mul_of_nonneg_left _ hlog` to reduce the goal to its premises. Use `(min_le_right _ _).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[inv_pow, div_eq_mul_inv]`. Use `_ ≤ (a0 : ℝ) * Real.log p + Real.log p * x * (2 * ((p : ℝ)⁻¹) ^ (a0 + 1)) := by`. Apply `add_le_add` to reduce the goal to its premises. Rewrite using `[Finset.sum_const, Nat.card_Icc]`. Simplify using the standard rewrite rules.

Rewrite using `[← Finset.mul_sum]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Apply `gl2a5_geom _ (by positivity)` to reduce the goal to its premises. Rewrite using `[inv_le_comm₀ hp0 (by norm_num)]`. Evaluate the numerical expressions.

Conclude with `hp.two_le`. Use `_ = _ := by`. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
lemma gl2a5s_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) (a0 : ℕ) :
    primeTermWeight x N p ≤ Real.log p * ((a0 : ℝ) + 2 * x / (p : ℝ) ^ (a0 + 1)) := by
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hcn : ∀ a ∈ Icc 1 N, cn x (p ^ a) = Real.log p * min 1 (x / (p : ℝ) ^ a) := by
    intro a ha
    rw [mem_Icc] at ha
    unfold cn
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    push_cast
    rfl
  calc primeTermWeight x N p ≤ ∑ a ∈ Icc 1 N, cn x (p ^ a) :=
        gl2a5_fiber_le N p (cn x) (gl2a5_cn_nonneg hx)
    _ = ∑ a ∈ Icc 1 N, Real.log p * min 1 (x / (p : ℝ) ^ a) := Finset.sum_congr rfl hcn
    _ ≤ ∑ a ∈ Icc 1 a0, Real.log p * min 1 (x / (p : ℝ) ^ a)
        + ∑ a ∈ Ioc a0 N, Real.log p * min 1 (x / (p : ℝ) ^ a) :=
        gl2a5_split _ (fun a => mul_nonneg hlog (le_min zero_le_one (by positivity))) a0 N
    _ ≤ ∑ a ∈ Icc 1 a0, Real.log p + ∑ a ∈ Ioc a0 N, Real.log p * x * ((p : ℝ)⁻¹) ^ a := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro a _
          exact mul_le_of_le_one_right hlog (min_le_left _ _)
        · apply Finset.sum_le_sum; intro a _
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hlog
          refine (min_le_right _ _).trans (le_of_eq ?_)
          rw [inv_pow, div_eq_mul_inv]
    _ ≤ (a0 : ℝ) * Real.log p + Real.log p * x * (2 * ((p : ℝ)⁻¹) ^ (a0 + 1)) := by
        apply add_le_add
        · rw [Finset.sum_const, Nat.card_Icc]; simp
        · rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply gl2a5_geom _ (by positivity)
          rw [inv_le_comm₀ hp0 (by norm_num)]
          norm_num
          exact hp.two_le
    _ = _ := by
        rw [inv_pow]; field_simp

/- English proof (translation)
Establish `hlog : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Establish `hfl : ⌊x⌋₊ ≠ 0`. Establish `: 1 ≤ ⌊x⌋₊` using `Nat.le_floor (by simpa using hx)`. Use linear arithmetic over natural numbers and integers.

Establish `h` using `gl2a5s_le (by linarith : (0 : ℝ) ≤ x) N hp (Nat.log p ⌊x⌋₊)`. Use `set a0 := Nat.log p ⌊x⌋₊`. Establish `h1 : (a0 : ℝ) * Real.log p ≤ Real.log x`. Rewrite using `[← Real.log_pow]`. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises.

Establish `: p ^ a0 ≤ ⌊x⌋₊` using `Nat.pow_log_le_self p hfl`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : x / (p : ℝ) ^ (a0 + 1) ≤ 1`. Rewrite using `[div_le_one (by positivity)]`. Establish `: ⌊x⌋₊ < p ^ (a0 + 1)` using `Nat.lt_pow_succ_log_self hp.one_lt _`.

Establish `h3 : x < (⌊x⌋₊ : ℝ) + 1` using `Nat.lt_floor_add_one x`. Establish `h4 : ((⌊x⌋₊ : ℝ) + 1) ≤ ((p ^ (a0 + 1) : ℕ) : ℝ)` using `by exact_mod_cast this`. Move the coercions through the operations in `at h4`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : Real.log p * ((a0 : ℝ) + 2 * x / (p : ℝ) ^ (a0 + 1)) = (a0 : ℝ) * Real.log p + 2 * Real.log p * (x / (p : ℝ) ^ (a0 + 1))` using `by ring`.

Establish `h6 : 2 * Real.log p * (x / (p : ℝ) ^ (a0 + 1)) ≤ 2 * Real.log p` using `mul_le_of_le_one_right (by positivity) h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma gl2a5s_le_small {x : ℝ} (hx : 1 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    primeTermWeight x N p ≤ Real.log x + 2 * Real.log p := by
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hfl : ⌊x⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
    omega
  have h := gl2a5s_le (by linarith : (0 : ℝ) ≤ x) N hp (Nat.log p ⌊x⌋₊)
  set a0 := Nat.log p ⌊x⌋₊
  have h1 : (a0 : ℝ) * Real.log p ≤ Real.log x := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    have : p ^ a0 ≤ ⌊x⌋₊ := Nat.pow_log_le_self p hfl
    calc ((p : ℝ) ^ a0) = ((p ^ a0 : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ x := Nat.floor_le (by linarith)
  have h2 : x / (p : ℝ) ^ (a0 + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : ⌊x⌋₊ < p ^ (a0 + 1) := Nat.lt_pow_succ_log_self hp.one_lt _
    have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h4 : ((⌊x⌋₊ : ℝ) + 1) ≤ ((p ^ (a0 + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h4
    linarith
  have h5 : Real.log p * ((a0 : ℝ) + 2 * x / (p : ℝ) ^ (a0 + 1)) =
      (a0 : ℝ) * Real.log p + 2 * Real.log p * (x / (p : ℝ) ^ (a0 + 1)) := by ring
  have h6 : 2 * Real.log p * (x / (p : ℝ) ^ (a0 + 1)) ≤ 2 * Real.log p :=
    mul_le_of_le_one_right (by positivity) h2
  linarith

/- English proof (translation)
Establish `h` using `gl2a5s_le hx N hp 0`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Nat.cast_zero, zero_add, pow_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma gl2a5s_le_large {x : ℝ} (hx : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    primeTermWeight x N p ≤ 2 * x * (Real.log p / p) := by
  have h := gl2a5s_le hx N hp 0
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_zero, zero_add, pow_one]
  ring

/- English proof (translation)
Establish `hx1 : 1 ≤ x` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `hL : 0 ≤ Real.log x` using `Real.log_nonneg hx1`. Distinguish the cases in `hp : p.Prime`. Break down `le_or_gt (p : ℝ) x with hpx | hpx` into its components or cases. Use `gl2a5s_le_small hx1 N hp` as an intermediate fact.

Establish `h2 : Real.log p ≤ Real.log x` using `Real.log_le_log (by exact_mod_cast hp.pos) hpx`. Combine the linear equalities and inequalities to obtain the conclusion. Use `gl2a5s_le_large (by linarith : (0 : ℝ) ≤ x) N hp` as an intermediate fact. Establish `h2 : Real.log p / p ≤ Real.log x / x` using `Real.log_div_self_antitoneOn (by simpa using hx) (by simpa using hx.trans hpx.le) hpx.le`. Establish `h3 : 2 * x * (Real.log p / p) ≤ 2 * x * (Real.log x / x)` using `mul_le_mul_of_nonneg_left h2 (by linarith)`.

Establish `h4 : 2 * x * (Real.log x / x) = 2 * Real.log x` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[gl2a5s_not_prime x N hp]`. Check the signs of the components of the expression.
-/
lemma gl2a5s_le_log {x : ℝ} (hx : Real.exp 1 ≤ x) (N p : ℕ) :
    primeTermWeight x N p ≤ 3 * Real.log x := by
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  by_cases hp : p.Prime
  · rcases le_or_gt (p : ℝ) x with hpx | hpx
    · have := gl2a5s_le_small hx1 N hp
      have h2 : Real.log p ≤ Real.log x := Real.log_le_log (by exact_mod_cast hp.pos) hpx
      linarith
    · have := gl2a5s_le_large (by linarith : (0 : ℝ) ≤ x) N hp
      have h2 : Real.log p / p ≤ Real.log x / x :=
        Real.log_div_self_antitoneOn (by simpa using hx) (by simpa using hx.trans hpx.le) hpx.le
      have h3 : 2 * x * (Real.log p / p) ≤ 2 * x * (Real.log x / x) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : 2 * x * (Real.log x / x) = 2 * Real.log x := by field_simp
      linarith
  · rw [gl2a5s_not_prime x N hp]; positivity

/- English proof (translation)
Rewrite using `[Finset.sum_boole]`. Establish `h1 : ((Icc 1 N).filter (fun p : ℕ => (p : ℝ) ≤ Y)).card ≤ (Icc 1 ⌊Y⌋₊).card`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [mem_filter, mem_Icc] at hp ⊢`.

Conclude with `⟨hp.1.1, Nat.le_floor hp.2⟩`. Rewrite `h1` using `[Nat.card_Icc]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h1` after adjusting the coercions. Use `_ = (⌊Y⌋₊ : ℝ) := by simp`.

Use `_ ≤ Y := Nat.floor_le hY`.
-/
lemma gl2a5_count (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    ∑ p ∈ Icc 1 N, (if (p : ℝ) ≤ Y then (1 : ℝ) else 0) ≤ Y := by
  rw [Finset.sum_boole]
  have h1 : ((Icc 1 N).filter (fun p : ℕ => (p : ℝ) ≤ Y)).card ≤ (Icc 1 ⌊Y⌋₊).card := by
    apply Finset.card_le_card
    intro p hp
    simp only [mem_filter, mem_Icc] at hp ⊢
    exact ⟨hp.1.1, Nat.le_floor hp.2⟩
  rw [Nat.card_Icc] at h1
  calc ((((Icc 1 N).filter (fun p : ℕ => (p : ℝ) ≤ Y)).card : ℕ) : ℝ) ≤ ((⌊Y⌋₊ + 1 - 1 : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = (⌊Y⌋₊ : ℝ) := by simp
    _ ≤ Y := Nat.floor_le hY

/- English proof (translation)
Simplify using `only [primesLeFinset, mem_filter, mem_Icc] at hn`. Rewrite using `[mem_Icc]`. Conclude with `⟨(Nat.minFac_pos n), (Nat.minFac_le hn.1.1).trans hn.1.2⟩`.
-/
lemma gl2a5_minFac_mem {N n : ℕ} (hn : n ∈ primesLeFinset N) : n.minFac ∈ Icc 1 N := by
  simp only [primesLeFinset, mem_filter, mem_Icc] at hn
  rw [mem_Icc]
  exact ⟨(Nat.minFac_pos n), (Nat.minFac_le hn.1.1).trans hn.1.2⟩

/- English proof (translation)
Establish `h1 : ∀ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' * (if n.minFac = n'.minFac then (1 : ℝ) else 0) = cn x n * primeTermWeight x N n.minFac`. Introduce `n _`. Unfold `primeTermWeight`. Rewrite using `[Finset.sum_filter, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `n' _`. Distinguish the cases in `h : n.minFac = n'.minFac`. Rewrite using `[if_pos h, if_pos h.symm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg (fun h' => h h'.symm)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl h1, ← Finset.sum_fiberwise_of_maps_to (fun n hn => gl2a5_minFac_mem hn)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p _`. Establish `h2 : ∀ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p), cn x n * primeTermWeight x N n.minFac = cn x n * primeTermWeight x N p`.

Introduce `n hn`. Rewrite using `[(mem_filter.1 hn).2]`. Rewrite using `[Finset.sum_congr rfl h2, ← Finset.sum_mul, sq]`. Both sides reduce to the same expression.
-/
lemma gl2a5_diag_eq (x : ℝ) (N : ℕ) :
    ∑ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' *
      (if n.minFac = n'.minFac then (1 : ℝ) else 0) = ∑ p ∈ Icc 1 N, (primeTermWeight x N p) ^ 2 := by
  have h1 : ∀ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' *
      (if n.minFac = n'.minFac then (1 : ℝ) else 0) = cn x n * primeTermWeight x N n.minFac := by
    intro n _
    unfold primeTermWeight
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n' _
    by_cases h : n.minFac = n'.minFac
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]; ring
  rw [Finset.sum_congr rfl h1,
    ← Finset.sum_fiberwise_of_maps_to (fun n hn => gl2a5_minFac_mem hn)]
  apply Finset.sum_congr rfl; intro p _
  have h2 : ∀ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p),
      cn x n * primeTermWeight x N n.minFac = cn x n * primeTermWeight x N p := by
    intro n hn
    rw [(mem_filter.1 hn).2]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, sq]
  rfl

/- English proof (translation)
Establish `h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1` using `Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith))`. Rewrite `h1` using `[Real.log_sqrt (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma gl2a5_log_le_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith))
  rw [Real.log_sqrt (by linarith)] at h1
  linarith

/- English proof (translation)
Establish `hx1 : 1 ≤ x` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `hL : 0 ≤ Real.log x` using `Real.log_nonneg hx1`. Establish `hpt : ∀ p ∈ Icc 1 ⌊x⌋₊, (primeTermWeight x N p) ^ 2 ≤ 3 * Real.log x * (4 * Λ p + Real.log x * (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0))`. Introduce `p _`. Establish `h0` using `gl2a5s_nonneg (by linarith : (0 : ℝ) ≤ x) N p`.

Establish `h3` using `gl2a5s_le_log hx N p`. Establish `h4 : primeTermWeight x N p ≤ 4 * Λ p + Real.log x * (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0)`. Distinguish the cases in `hp : p.Prime`. Establish `h5` using `gl2a5s_le_small hx1 N hp`. Establish `hlog : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`.

Rewrite using `[vonMangoldt_apply_prime hp]`. Use `split_ifs with hs`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Establish `h6 : x < (p : ℝ) ^ 2` using `(Real.sqrt_lt' hp0).1 (not_le.1 hs)`.

Establish `h7 : Real.log x ≤ Real.log ((p : ℝ) ^ 2)` using `Real.log_le_log (by linarith) h6.le`. Rewrite `h7` using `[Real.log_pow]`. Move the coercions through the operations in `at h7`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[gl2a5s_not_prime x N hp]`.

Establish `: 0 ≤ Λ p` using `vonMangoldt_nonneg`. Apply the tactic sequence `split_ifs <;> positivity`. Rewrite using `[sq]`. Conclude with `mul_le_mul h3 h4 h0 (by positivity)`. Use `(Finset.sum_le_sum hpt).trans ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]`. Establish `h1` using `hψ ⌊x⌋₊`. Establish `h2 : (⌊x⌋₊ : ℝ) ≤ x` using `Nat.floor_le (by linarith)`. Establish `h3` using `gl2a5_count ⌊x⌋₊ (Real.sqrt x) (Real.sqrt_nonneg x)`. Establish `h4` using `gl2a5_log_le_sqrt hx1`.

Apply the tactic sequence `have h5 : Real.log x * (∑ p ∈ Icc 1 ⌊x⌋₊, (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0)) ≤ 2 * Real.sqrt x * Real.sqrt x := mul_le_mul h4 h3 (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (by positivity)`. Rewrite `h5` using `[mul_assoc, Real.mul_self_sqrt (by linarith)]`. Establish `h6 : 4 * ∑ i ∈ Icc 1 ⌊x⌋₊, Λ i + Real.log x * (∑ p ∈ Icc 1 ⌊x⌋₊, (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0)) ≤ 10 * x` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma gl2a5_diag_small (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ}
    (hx : Real.exp 1 ≤ x) (N : ℕ) :
    ∑ p ∈ Icc 1 ⌊x⌋₊, (primeTermWeight x N p) ^ 2 ≤ 30 * x * Real.log x := by
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpt : ∀ p ∈ Icc 1 ⌊x⌋₊, (primeTermWeight x N p) ^ 2 ≤
      3 * Real.log x * (4 * Λ p + Real.log x * (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0)) := by
    intro p _
    have h0 := gl2a5s_nonneg (by linarith : (0 : ℝ) ≤ x) N p
    have h3 := gl2a5s_le_log hx N p
    have h4 : primeTermWeight x N p ≤
        4 * Λ p + Real.log x * (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0) := by
      by_cases hp : p.Prime
      · have h5 := gl2a5s_le_small hx1 N hp
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        rw [vonMangoldt_apply_prime hp]
        split_ifs with hs
        · linarith
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
          have h6 : x < (p : ℝ) ^ 2 := (Real.sqrt_lt' hp0).1 (not_le.1 hs)
          have h7 : Real.log x ≤ Real.log ((p : ℝ) ^ 2) := Real.log_le_log (by linarith) h6.le
          rw [Real.log_pow] at h7
          push_cast at h7
          linarith
      · rw [gl2a5s_not_prime x N hp]
        have : 0 ≤ Λ p := vonMangoldt_nonneg
        split_ifs <;> positivity
    rw [sq]
    exact mul_le_mul h3 h4 h0 (by positivity)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := hψ ⌊x⌋₊
  have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h3 := gl2a5_count ⌊x⌋₊ (Real.sqrt x) (Real.sqrt_nonneg x)
  have h4 := gl2a5_log_le_sqrt hx1
  have h5 : Real.log x * (∑ p ∈ Icc 1 ⌊x⌋₊, (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0)) ≤
      2 * Real.sqrt x * Real.sqrt x :=
    mul_le_mul h4 h3 (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (by positivity)
  rw [mul_assoc, Real.mul_self_sqrt (by linarith)] at h5
  have h6 : 4 * ∑ i ∈ Icc 1 ⌊x⌋₊, Λ i + Real.log x *
      (∑ p ∈ Icc 1 ⌊x⌋₊, (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0)) ≤ 10 * x := by linarith
  calc _ ≤ 3 * Real.log x * (10 * x) := mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by ring

/- English proof (translation)
Establish `hn3 : (3 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `he : Real.exp 1 ≤ n` using `by linarith [Real.exp_one_lt_d9]`. Establish `h1 : Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ Real.log n / n`. Apply `Real.log_div_self_antitoneOn (by simpa using he)` to reduce the goal to its premises. Use `show Real.exp 1 ≤ _ push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 / n`. Apply `one_div_le_one_div_of_le (by linarith)` to reduce the goal to its premises.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : 0 ≤ Real.log n / n`. Use `Real.log_natCast_nonneg n` as an intermediate fact. Check the signs of the components of the expression.

Establish `h4` using `mul_le_mul h1 h2 (by positivity) h3`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sq, div_mul_div_comm, mul_one]`. Use `_ ≤ _ := h4`. Use `_ = _ := by rw [sq, div_mul_div_comm, mul_one]`.
-/
lemma gl2a5_g_anti {n : ℕ} (hn : 3 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ Real.log n / (n : ℝ) ^ 2 := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ n := by linarith [Real.exp_one_lt_d9]
  have h1 : Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ Real.log n / n := by
    apply Real.log_div_self_antitoneOn (by simpa using he)
    · show Real.exp 1 ≤ _
      push_cast; linarith
    · push_cast; linarith
  have h2 : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 / n := by
    apply one_div_le_one_div_of_le (by linarith)
    push_cast; linarith
  have h3 : 0 ≤ Real.log n / n := by
    have := Real.log_natCast_nonneg n
    positivity
  have h4 := mul_le_mul h1 h2 (by positivity) h3
  calc _ = Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) := by
        rw [sq, div_mul_div_comm, mul_one]
    _ ≤ _ := h4
    _ = _ := by rw [sq, div_mul_div_comm, mul_one]

/- English proof (translation)
Establish `he : Real.exp 1 ≤ x` using `by linarith [Real.exp_one_lt_d9]`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hL : 1 ≤ Real.log x`. Rewrite using `[Real.le_log_iff_exp_le hx0]`. Conclude with `he`.

Establish `hK : 3 ≤ ⌊x⌋₊` using `Nat.le_floor (by simpa using hx)`. Use `set K := ⌊x⌋₊ with hKdef`. Establish `hpt : ∀ p ∈ Ioc K N, (primeTermWeight x N p) ^ 2 ≤ 4 * x ^ 2 * (Λ p * (Real.log p / (p : ℝ) ^ 2))`. Introduce `p _`. Establish `hlog : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`.

Distinguish the cases in `hp : p.Prime`. Establish `h0` using `gl2a5s_nonneg hx0.le N p`. Establish `h1` using `gl2a5s_le_large hx0.le N hp`. Rewrite using `[vonMangoldt_apply_prime hp]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[gl2a5s_not_prime x N hp]`. Establish `: 0 ≤ Λ p` using `vonMangoldt_nonneg`. Establish `h : 0 ≤ 4 * x ^ 2 * (Λ p * (Real.log p / (p : ℝ) ^ 2))` using `by positivity`. Simplify using `using h`. Use `(Finset.sum_le_sum hpt).trans ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum]`. Establish `h1` using `gl2a5_abel hψ (fun n => Real.log n / (n : ℝ) ^ 2) K (fun n hn => gl2a5_g_anti (by omega)) (fun n _ => by`. Use `Real.log_natCast_nonneg n` as an intermediate fact. Use the proof step `positivity) N`. Establish `h2` using `gl2a5_log_sq_tail (K + 1) (by omega) N`.

Establish `hy : x < ((K + 1 : ℕ) : ℝ)` using `by push_cast; exact Nat.lt_floor_add_one x`. Use `set y : ℝ := ((K + 1 : ℕ) : ℝ) with hydef`. Establish `hy0 : 0 < y` using `by linarith`. Establish `h3 : Real.log y / y ≤ Real.log x / x` using `Real.log_div_self_antitoneOn (by simpa using he) (by simpa using he.trans hy.le) hy.le`. Establish `h4 : 1 / y ≤ 1 / x` using `one_div_le_one_div_of_le hx0 hy.le`.

Establish `e1 : 2 * ((K : ℝ) + 1) * (Real.log y / y ^ 2) = 2 * (Real.log y / y)`. Establish `: (K : ℝ) + 1 = y` using `by rw [hydef]; push_cast; rfl`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Establish `e2 : (Real.log y + 2) / y = Real.log y / y + 2 * (1 / y)` using `by ring`.

Rewrite `h1` using `[e1]`. Rewrite `h2` using `[e2]`. Establish `h5 : ∑ n ∈ Ioc K N, Λ n * (Real.log n / (n : ℝ) ^ 2) ≤ 4 * (Real.log x / x) + 4 * (1 / x)`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
lemma gl2a5_diag_large (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ}
    (hx : 3 ≤ x) (N : ℕ) :
    ∑ p ∈ Ioc ⌊x⌋₊ N, (primeTermWeight x N p) ^ 2 ≤ 32 * x * Real.log x := by
  have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact he
  have hK : 3 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  set K := ⌊x⌋₊ with hKdef
  have hpt : ∀ p ∈ Ioc K N, (primeTermWeight x N p) ^ 2 ≤
      4 * x ^ 2 * (Λ p * (Real.log p / (p : ℝ) ^ 2)) := by
    intro p _
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    by_cases hp : p.Prime
    · have h0 := gl2a5s_nonneg hx0.le N p
      have h1 := gl2a5s_le_large hx0.le N hp
      rw [vonMangoldt_apply_prime hp]
      calc (primeTermWeight x N p) ^ 2 ≤ (2 * x * (Real.log p / p)) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = _ := by ring
    · rw [gl2a5s_not_prime x N hp]
      have : 0 ≤ Λ p := vonMangoldt_nonneg
      have h : 0 ≤ 4 * x ^ 2 * (Λ p * (Real.log p / (p : ℝ) ^ 2)) := by positivity
      simpa using h
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  have h1 := gl2a5_abel hψ (fun n => Real.log n / (n : ℝ) ^ 2) K
    (fun n hn => gl2a5_g_anti (by omega))
    (fun n _ => by
      have := Real.log_natCast_nonneg n
      positivity) N
  have h2 := gl2a5_log_sq_tail (K + 1) (by omega) N
  have hy : x < ((K + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one x
  set y : ℝ := ((K + 1 : ℕ) : ℝ) with hydef
  have hy0 : 0 < y := by linarith
  have h3 : Real.log y / y ≤ Real.log x / x :=
    Real.log_div_self_antitoneOn (by simpa using he) (by simpa using he.trans hy.le) hy.le
  have h4 : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hy.le
  have e1 : 2 * ((K : ℝ) + 1) * (Real.log y / y ^ 2) = 2 * (Real.log y / y) := by
    have : (K : ℝ) + 1 = y := by rw [hydef]; push_cast; rfl
    rw [this]; field_simp
  have e2 : (Real.log y + 2) / y = Real.log y / y + 2 * (1 / y) := by ring
  rw [e1] at h1
  rw [e2] at h2
  have h5 : ∑ n ∈ Ioc K N, Λ n * (Real.log n / (n : ℝ) ^ 2) ≤ 4 * (Real.log x / x) + 4 * (1 / x) := by
    linarith
  calc _ ≤ 4 * x ^ 2 * (4 * (Real.log x / x) + 4 * (1 / x)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = 16 * x * Real.log x + 16 * x := by field_simp; ring
    _ ≤ _ := by nlinarith

/- English proof (translation)
Establish `he : Real.exp 1 ≤ x` using `by linarith [Real.exp_one_lt_d9]`. Establish `h1` using `gl2a5_split (fun p => (primeTermWeight x N p) ^ 2) (fun p => by positivity) ⌊x⌋₊ N`. Establish `h2` using `gl2a5_diag_small hψ he N`. Establish `h3` using `gl2a5_diag_large hψ hx N`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma gl2a5_diag_le (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ}
    (hx : 3 ≤ x) (N : ℕ) :
    ∑ p ∈ Icc 1 N, (primeTermWeight x N p) ^ 2 ≤ 62 * x * Real.log x := by
  have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  have h1 := gl2a5_split (fun p => (primeTermWeight x N p) ^ 2) (fun p => by positivity) ⌊x⌋₊ N
  have h2 := gl2a5_diag_small hψ he N
  have h3 := gl2a5_diag_large hψ hx N
  linarith

/- English proof (translation)
Establish `hx1 : 1 ≤ x` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `hL : 0 ≤ Real.log x` using `Real.log_nonneg hx1`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (fun n hn => gl2a5_minFac_mem (N := N) (mem_filter.1 hn).1)]`. Establish `hpt : ∀ p ∈ Icc 1 N, ∑ n ∈ ((primesLeFinset N).filter (fun n => n.minFac ∣ m₀)).filter (fun n => n.minFac = p), cn x n ≤ (if (p : ℝ) ≤ Y then (1 : ℝ) else 0) * (3 * Real.log x)`. Introduce `p hpN`.

Distinguish the cases in `hp : p.Prime ∧ p ∣ m₀`. Rewrite using `[if_pos (h p hp.1 hp.2 (mem_Icc.1 hpN).2), one_mul]`. Use `le_trans ?_ (gl2a5s_le_log hx N p)` and prove the remaining obligations. Unfold `primeTermWeight`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises.

Introduce `n hn`. Simplify using `only [mem_filter] at hn ⊢`. Conclude with `⟨hn.1.1, hn.2⟩`. Introduce `n _ _; exact gl2a5_cn_nonneg (by linarith) n`. Establish `: ((primesLeFinset N).filter (fun n => n.minFac ∣ m₀)).filter (fun n => n.minFac = p) = ∅`.

Apply `Finset.filter_eq_empty_iff.2` to reduce the goal to its premises. Introduce `n hn hmf`. Simplify using `only [primesLeFinset, mem_filter] at hn`. Conclude with `hp ⟨hmf ▸ Nat.minFac_prime hn.1.2.ne_one, hmf ▸ hn.2⟩`. Rewrite using `[this, Finset.sum_empty]`.

Apply the tactic sequence `split_ifs <;> positivity`. Use `(Finset.sum_le_sum hpt).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`. Conclude with `mul_le_mul_of_nonneg_right (gl2a5_count N Y hY) (by positivity)`.
-/
lemma small_prime_factor_sum_bound {x : ℝ} (hx : Real.exp 1 ≤ x) (N m₀ : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (h : ∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ Y) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac ∣ m₀), cn x n ≤ Y * (3 * Real.log x) := by
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun n hn => gl2a5_minFac_mem (N := N) (mem_filter.1 hn).1)]
  have hpt : ∀ p ∈ Icc 1 N, ∑ n ∈ ((primesLeFinset N).filter (fun n => n.minFac ∣ m₀)).filter
      (fun n => n.minFac = p), cn x n ≤ (if (p : ℝ) ≤ Y then (1 : ℝ) else 0) * (3 * Real.log x) := by
    intro p hpN
    by_cases hp : p.Prime ∧ p ∣ m₀
    · rw [if_pos (h p hp.1 hp.2 (mem_Icc.1 hpN).2), one_mul]
      refine le_trans ?_ (gl2a5s_le_log hx N p)
      unfold primeTermWeight
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [mem_filter] at hn ⊢
        exact ⟨hn.1.1, hn.2⟩
      · intro n _ _; exact gl2a5_cn_nonneg (by linarith) n
    · have : ((primesLeFinset N).filter (fun n => n.minFac ∣ m₀)).filter (fun n => n.minFac = p) = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        intro n hn hmf
        simp only [primesLeFinset, mem_filter] at hn
        exact hp ⟨hmf ▸ Nat.minFac_prime hn.1.2.ne_one, hmf ▸ hn.2⟩
      rw [this, Finset.sum_empty]
      split_ifs <;> positivity
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (gl2a5_count N Y hY) (by positivity)

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hs1 : 1 ≤ Real.sqrt x` using `Real.one_le_sqrt.2 hx`. Establish `hK : 1 ≤ ⌊Real.sqrt x⌋₊` using `Nat.le_floor (by simpa using hs1)`. Use `set K := ⌊Real.sqrt x⌋₊ with hKdef`. Establish `hcn : ∀ m ∈ Icc 1 N, cn x (m ^ 2) = Λ m * min 1 (x / (m : ℝ) ^ 2)`.

Introduce `m _`. Unfold `cn`. Rewrite using `[vonMangoldt_apply_pow (by norm_num)]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hΛ : ∀ m : ℕ, 0 ≤ Λ m` using `fun m => vonMangoldt_nonneg`. Establish `hy : Real.sqrt x < ((K + 1 : ℕ) : ℝ)` using `by push_cast; exact Nat.lt_floor_add_one _`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `n hn`.

Simplify using `only [primesLeFinset, mem_filter, mem_Icc] at hn`. Take `⟨⟨⟨h1, hN⟩, _⟩, m, rfl⟩` from `hn`. Rewrite using `[mem_image]`. Use `⟨m, ?_, by ring⟩` and prove the remaining obligations. Rewrite using `[mem_Icc]`.

Establish `hm : 1 ≤ m`. Break down `Nat.eq_zero_or_pos m with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Simplify using `at h1`. Conclude with `h0`.

Conclude with `⟨hm, (Nat.le_mul_self m).trans hN⟩`. Introduce `n _ _`. Conclude with `gl2a5_cn_nonneg hx0.le n`. Use `_ = ∑ m ∈ Icc 1 N, cn x (m ^ 2) := by`. Apply `Finset.sum_image` to reduce the goal to its premises.

Introduce `a _ b _ hab`. Conclude with `Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hab`. Use `_ = ∑ m ∈ Icc 1 N, Λ m * min 1 (x / (m : ℝ) ^ 2) := Finset.sum_congr rfl hcn`. Use `_ ≤ ∑ m ∈ Icc 1 K, Λ m * min 1 (x / (m : ℝ) ^ 2) + ∑ m ∈ Ioc K N, Λ m * min 1 (x / (m : ℝ) ^ 2) := gl2a5_split _ (fun m => mul_nonneg (hΛ m) (le_min zero_le_one (by positivity))) K N`. Use `_ ≤ ∑ m ∈ Icc 1 K, Λ m + x * ∑ m ∈ Ioc K N, Λ m * (1 / (m : ℝ) ^ 2) := by`.

Apply `add_le_add` to reduce the goal to its premises. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `m _`. Conclude with `mul_le_of_le_one_right (hΛ m) (min_le_left _ _)`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `m _`. Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ 2 * Real.sqrt x + x * (4 / Real.sqrt x) := by`. Apply `add_le_add` to reduce the goal to its premises.

Conclude with `(hψ K).trans (by linarith [Nat.floor_le (Real.sqrt_nonneg x)])`. Apply `mul_le_mul_of_nonneg_left _ hx0.le` to reduce the goal to its premises. Establish `h1` using `gl2a5_abel hψ (fun n => 1 / (n : ℝ) ^ 2) K (fun n hn => by`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast (by omega : 0 < n)`. Apply `one_div_le_one_div_of_le (by positivity)` to reduce the goal to its premises.

Use `push_cast`. Use the proof step `nlinarith)`. Use the proof step `(fun n _ => by positivity) N`. Establish `h2` using `gl2a5_inv_sq_tail (K + 1) (by omega) N`. Use `set y : ℝ := ((K + 1 : ℕ) : ℝ) with hydef`.

Establish `hy0 : 0 < y` using `by linarith`. Establish `e1 : 2 * ((K : ℝ) + 1) * (1 / y ^ 2) = 2 * (1 / y)`. Establish `: (K : ℝ) + 1 = y` using `by rw [hydef]; push_cast; rfl`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.

Rewrite `h1` using `[e1]`. Establish `h4 : 1 / y ≤ 1 / Real.sqrt x` using `one_div_le_one_div_of_le (by linarith) hy.le`. Establish `e2 : 4 / Real.sqrt x = 4 * (1 / Real.sqrt x)` using `by ring`. Rewrite using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `_ = 6 * Real.sqrt x := by`. Establish `: x * (4 / Real.sqrt x) = 4 * Real.sqrt x`. Establish `hs0 : Real.sqrt x ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Real.sq_sqrt hx0.le]`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma square_terms_sum_le_sqrt (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => IsSquare n), cn x n ≤ 6 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
  have hK : 1 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (by simpa using hs1)
  set K := ⌊Real.sqrt x⌋₊ with hKdef
  have hcn : ∀ m ∈ Icc 1 N, cn x (m ^ 2) = Λ m * min 1 (x / (m : ℝ) ^ 2) := by
    intro m _
    unfold cn
    rw [vonMangoldt_apply_pow (by norm_num)]
    push_cast
    rfl
  have hΛ : ∀ m : ℕ, 0 ≤ Λ m := fun m => vonMangoldt_nonneg
  have hy : Real.sqrt x < ((K + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  calc ∑ n ∈ (primesLeFinset N).filter (fun n => IsSquare n), cn x n
      ≤ ∑ n ∈ (Icc 1 N).image (fun m => m ^ 2), cn x n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [primesLeFinset, mem_filter, mem_Icc] at hn
          obtain ⟨⟨⟨h1, hN⟩, _⟩, m, rfl⟩ := hn
          rw [mem_image]
          refine ⟨m, ?_, by ring⟩
          rw [mem_Icc]
          have hm : 1 ≤ m := by
            rcases Nat.eq_zero_or_pos m with h0 | h0
            · subst h0; simp at h1
            · exact h0
          exact ⟨hm, (Nat.le_mul_self m).trans hN⟩
        · intro n _ _; exact gl2a5_cn_nonneg hx0.le n
    _ = ∑ m ∈ Icc 1 N, cn x (m ^ 2) := by
        apply Finset.sum_image
        intro a _ b _ hab
        exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hab
    _ = ∑ m ∈ Icc 1 N, Λ m * min 1 (x / (m : ℝ) ^ 2) := Finset.sum_congr rfl hcn
    _ ≤ ∑ m ∈ Icc 1 K, Λ m * min 1 (x / (m : ℝ) ^ 2)
        + ∑ m ∈ Ioc K N, Λ m * min 1 (x / (m : ℝ) ^ 2) :=
        gl2a5_split _ (fun m => mul_nonneg (hΛ m) (le_min zero_le_one (by positivity))) K N
    _ ≤ ∑ m ∈ Icc 1 K, Λ m + x * ∑ m ∈ Ioc K N, Λ m * (1 / (m : ℝ) ^ 2) := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro m _
          exact mul_le_of_le_one_right (hΛ m) (min_le_left _ _)
        · rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro m _
          calc Λ m * min 1 (x / (m : ℝ) ^ 2) ≤ Λ m * (x / (m : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) (hΛ m)
            _ = _ := by ring
    _ ≤ 2 * Real.sqrt x + x * (4 / Real.sqrt x) := by
        apply add_le_add
        · exact (hψ K).trans (by linarith [Nat.floor_le (Real.sqrt_nonneg x)])
        · apply mul_le_mul_of_nonneg_left _ hx0.le
          have h1 := gl2a5_abel hψ (fun n => 1 / (n : ℝ) ^ 2) K
            (fun n hn => by
              have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
              apply one_div_le_one_div_of_le (by positivity)
              push_cast
              nlinarith)
            (fun n _ => by positivity) N
          have h2 := gl2a5_inv_sq_tail (K + 1) (by omega) N
          set y : ℝ := ((K + 1 : ℕ) : ℝ) with hydef
          have hy0 : 0 < y := by linarith
          have e1 : 2 * ((K : ℝ) + 1) * (1 / y ^ 2) = 2 * (1 / y) := by
            have : (K : ℝ) + 1 = y := by rw [hydef]; push_cast; rfl
            rw [this]; field_simp
          rw [e1] at h1
          have h4 : 1 / y ≤ 1 / Real.sqrt x := one_div_le_one_div_of_le (by linarith) hy.le
          have e2 : 4 / Real.sqrt x = 4 * (1 / Real.sqrt x) := by ring
          rw [e2]
          linarith
    _ = 6 * Real.sqrt x := by
        have : x * (4 / Real.sqrt x) = 4 * Real.sqrt x := by
          have hs0 : Real.sqrt x ≠ 0 := by positivity
          field_simp
          rw [Real.sq_sqrt hx0.le]
        rw [this]; ring

/- English proof (translation)
Establish `hx1 : 1 ≤ x` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `h1` using `small_prime_factor_sum_bound hx N m₀ Y hY h`. Establish `h2` using `square_terms_sum_le_sqrt hψ hx1 N`. Establish `h3` using `Finset.sum_union_inter (s₁ := (primesLeFinset N).filter (fun n => n.minFac ∣ m₀)) (s₂ := (primesLeFinset N).filter (fun n => IsSquare n)) (f := cn x)`. Establish `h4 : 0 ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac ∣ m₀) ∩ (primesLeFinset N).filter (fun n => IsSquare n), cn x n` using `Finset.sum_nonneg (fun n _ => gl2a5_cn_nonneg (by linarith) n)`.

Establish `h5 : ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac ∣ m₀) ∪ (primesLeFinset N).filter (fun n => IsSquare n), cn x n`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `n hn`. Rewrite `hn` using `[mem_filter]`. Establish `hpp : IsPrimePow n` using `(mem_filter.1 hn.1).2`.

Rewrite using `[mem_union, mem_filter, mem_filter]`. Break down `gl2a5_out_one m₀ hpp hn.2 with hd | ⟨m, hm⟩` into its components or cases. Conclude with `Or.inl ⟨hn.1, hd⟩`. Conclude with `Or.inr ⟨hn.1, ⟨m, by rw [hm, sq]⟩⟩`. Introduce `n _ _; exact gl2a5_cn_nonneg (by linarith) n`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma gl2a5_R_le (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ}
    (hx : Real.exp 1 ≤ x) (N m₀ : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (h : ∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ Y) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n ≤
      Y * (3 * Real.log x) + 6 * Real.sqrt x := by
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1 := small_prime_factor_sum_bound hx N m₀ Y hY h
  have h2 := square_terms_sum_le_sqrt hψ hx1 N
  have h3 := Finset.sum_union_inter (s₁ := (primesLeFinset N).filter (fun n => n.minFac ∣ m₀))
    (s₂ := (primesLeFinset N).filter (fun n => IsSquare n)) (f := cn x)
  have h4 : 0 ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac ∣ m₀) ∩
      (primesLeFinset N).filter (fun n => IsSquare n), cn x n :=
    Finset.sum_nonneg (fun n _ => gl2a5_cn_nonneg (by linarith) n)
  have h5 : ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n ≤
      ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac ∣ m₀) ∪
        (primesLeFinset N).filter (fun n => IsSquare n), cn x n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [mem_filter] at hn
      have hpp : IsPrimePow n := (mem_filter.1 hn.1).2
      rw [mem_union, mem_filter, mem_filter]
      rcases gl2a5_out_one m₀ hpp hn.2 with hd | ⟨m, hm⟩
      · exact Or.inl ⟨hn.1, hd⟩
      · exact Or.inr ⟨hn.1, ⟨m, by rw [hm, sq]⟩⟩
    · intro n _ _; exact gl2a5_cn_nonneg (by linarith) n
  linarith

/- English proof (translation)
Unfold `primesLeFinset`. Use `symm`. Apply `Finset.sum_filter_of_ne` to reduce the goal to its premises. Introduce `n _ hne`. Assume the negation of the conclusion as `hpp`.

Conclude with `hne (by rw [gl2a5_cn_zero x hpp, zero_mul])`.
-/
lemma gl2a5_restrict (x : ℝ) (N : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, cn x n * F n = ∑ n ∈ primesLeFinset N, cn x n * F n := by
  unfold primesLeFinset
  symm
  apply Finset.sum_filter_of_ne
  intro n _ hne
  by_contra hpp
  exact hne (by rw [gl2a5_cn_zero x hpp, zero_mul])

/- English proof (translation)
Establish `h1 : ∀ (S : Finset ℕ) (n : ℕ), ∑ n' ∈ S, cn x n * cn x n' * G n n' = cn x n * ∑ n' ∈ S, cn x n' * G n n'`. Introduce `S n`. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n' _`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1]`. Rewrite using `[gl2a5_restrict]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`.

Rewrite using `[gl2a5_restrict]`.
-/
lemma gl2a5_restrict2 (x : ℝ) (N : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, cn x n * cn x n' * G n n' =
      ∑ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' * G n n' := by
  have h1 : ∀ (S : Finset ℕ) (n : ℕ), ∑ n' ∈ S, cn x n * cn x n' * G n n' =
      cn x n * ∑ n' ∈ S, cn x n' * G n n' := by
    intro S n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n' _; ring
  simp only [h1]
  rw [gl2a5_restrict]
  apply Finset.sum_congr rfl; intro n _
  rw [gl2a5_restrict]

/- English proof (translation)
Distinguish the cases in `hd : d = 1`. Substitute `hd` using the available equality. Combine the linear relations using `[gl2a5s_nonneg hx N 1]`. Establish `h1 : ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n ≤ primeTermWeight x N d`. Unfold `primeTermWeight`.

Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `n hn`. Rewrite `hn`, the goal using `[mem_filter]`. Establish `hpp : IsPrimePow n` using `(mem_filter.1 hn.1).2`. Use `⟨hn.1, ?_⟩` and prove the remaining obligations.

Break down `gl2a5_out_cases m₀ hpp with h | h` into its components or cases. Conclude with `absurd (hn.2.symm.trans h) hd`. Rewrite using `[← h]`. Conclude with `hn.2`. Introduce `n _ _`.

Conclude with `gl2a5_cn_nonneg hx n`. Establish `h2 : 0 ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n` using `Finset.sum_nonneg (fun n _ => gl2a5_cn_nonneg hx n)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma gl2a5_W_le {x : ℝ} (hx : 0 ≤ x) (N m₀ d : ℕ) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n ≤
      ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n + primeTermWeight x N d := by
  by_cases hd : d = 1
  · subst hd
    linarith [gl2a5s_nonneg hx N 1]
  · have h1 : ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n ≤ primeTermWeight x N d := by
      unfold primeTermWeight
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [mem_filter] at hn ⊢
        have hpp : IsPrimePow n := (mem_filter.1 hn.1).2
        refine ⟨hn.1, ?_⟩
        rcases gl2a5_out_cases m₀ hpp with h | h
        · exact absurd (hn.2.symm.trans h) hd
        · rw [← h]; exact hn.2
      · intro n _ _; exact gl2a5_cn_nonneg hx n
    have h2 : 0 ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n :=
      Finset.sum_nonneg (fun n _ => gl2a5_cn_nonneg hx n)
    linarith

/- English proof (translation)
The claim follows from `|(∑ q ∈ PPs, (jacobiSym a q : ℝ)) / PPs.card| ≤ 1 := by rw [abs_div, Nat.abs_cast] apply div_le_one_of_le₀ _ (Nat.cast_nonneg _) refine (Finset.abs_sum_le_sum_abs _ _).trans ?_ calc ∑ q ∈ PPs, |(jacobiSym a q : ℝ)| ≤ ∑ q ∈ PPs, (1 : ℝ) := by apply Finset.sum_le_sum; intro q _ rca …`.
-/
lemma gl2a5_mean_le_one (PPs : Finset ℕ) (a : ℤ) :
    |(∑ q ∈ PPs, (jacobiSym a q : ℝ)) / PPs.card| ≤ 1 := by
  rw [abs_div, Nat.abs_cast]
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ q ∈ PPs, |(jacobiSym a q : ℝ)| ≤ ∑ q ∈ PPs, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro q _
        rcases jacobiSym.trichotomy a q with h | h | h <;> rw [h] <;> simp
    _ = PPs.card := by simp

/- English proof (translation)
Introduce `hψ ε hε0 hε1 C' c' hC' hc'`. Use `⟨max 3 (Real.exp (800 / c')), 4 * C' + 1286, ?_⟩` and prove the remaining obligations. Introduce `x hx m₀ PPs κ nStar _ _ hm₀p hne hPP _ _ hκn hμ`. Establish `hx3 : 3 ≤ x` using `(le_max_left _ _).trans hx`. Establish `hxe : Real.exp (800 / c') ≤ x` using `(le_max_right _ _).trans hx`.

Establish `he : Real.exp 1 ≤ x` using `by linarith [Real.exp_one_lt_d9]`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1 : 1 ≤ x` using `by linarith`. Establish `hL1 : 1 ≤ Real.log x` using `by rw [Real.le_log_iff_exp_le hx0]; exact he`. Establish `hLc : 800 / c' ≤ Real.log x` using `by rw [Real.le_log_iff_exp_le hx0]; exact hxe`.

Establish `hψN : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)`. Introduce `M`. Use `hψ M (Nat.cast_nonneg M)` as an intermediate fact. Rewrite `this` using `[Nat.floor_natCast]`. Then use the resulting hypothesis. Establish `hcard : (0 : ℝ) < PPs.card` using `by exact_mod_cast Finset.card_pos.2 hne`.

Simplify using `only [sqSum]`. Use `set N := ⌊x ^ (400 : ℝ)⌋₊ with hN`. Establish `hNz : (N : ℝ) ≤ x ^ (400 : ℝ)` using `Nat.floor_le (by positivity)`. Use `set δ := C' * Real.exp (-c' * Real.log x ^ 2) with hδ`. Establish `hδ0 : 0 ≤ δ` using `by positivity`.

Establish `hcn0 : ∀ n, 0 ≤ cn x n` using `gl2a5_cn_nonneg hx0.le`. Establish `ha : ∀ n, ‖(cn x n : ℂ) * κ n‖ ≤ cn x n`. Introduce `n`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (hcn0 n)]`. Conclude with `mul_le_of_le_one_right (hcn0 n) (hκn n)`.

Establish `step1` using `gl2a5_expand (Icc 1 N) PPs (fun n => (cn x n : ℂ) * κ n) (cn x) ha`. Establish `step2 : (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, cn x n * cn x n' * |∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)|) / PPs.card = ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, cn x n * cn x n' * |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card|`. Rewrite using `[Finset.sum_div]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`.

Rewrite using `[Finset.sum_div]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n' _`. Rewrite using `[abs_div, Nat.abs_cast, mul_div_assoc]`. Establish `step3` using `gl2a5_restrict2 x N (fun n n' => |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card|)`.

Establish `step4` using `gl2a5_comb (primesLeFinset N) (cn x) hcn0 (outPart m₀) Nat.minFac (fun n n' => (∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card) δ nStar.minFac (nStar / nStar.minFac) (by`. Introduce `n hn n' hn'`. Establish `hn2` using `mem_filter.1 hn`. Establish `hn2'` using `mem_filter.1 hn'`. Conclude with `gl2a5_pointwise m₀ nStar hn2.2 hn2'.2 _ δ hδ0 (gl2a5_mean_le_one PPs _) (fun h1 h2 => hμ n n' hn2.1 hn2'.1 hn2.2 hn2'.2 h1 h2))`.

Rewrite `step4` using `[gl2a5_diag_eq]`. Use `set s := Real.sqrt x with hs`. Establish `hs1 : 1 ≤ s` using `Real.one_le_sqrt.2 hx1`. Establish `hss : s * s = x` using `Real.mul_self_sqrt hx0.le`. Establish `hLs : Real.log x ≤ 2 * s` using `gl2a5_log_le_sqrt hx1`.

Establish `hD` using `gl2a5_diag_le hψN hx3 N`. Establish `hsum : ∑ n ∈ primesLeFinset N, cn x n ≤ 2 * x ^ (400 : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum0 : 0 ≤ ∑ n ∈ primesLeFinset N, cn x n` using `Finset.sum_nonneg (fun n _ => hcn0 n)`. Establish `hgen : δ * (∑ n ∈ primesLeFinset N, cn x n) ^ 2 ≤ 4 * C'`.

Establish `h1 : (∑ n ∈ primesLeFinset N, cn x n) ^ 2 ≤ (2 * x ^ (400 : ℝ)) ^ 2` using `pow_le_pow_left₀ hsum0 hsum 2`. Establish `h2 : (2 * x ^ (400 : ℝ)) ^ 2 = 4 * Real.exp (800 * Real.log x)`. Rewrite using `[Real.rpow_def_of_pos hx0, mul_pow, ← Real.exp_nat_mul]`. Evaluate the numerical expressions. Put the polynomial expressions in normal form.

Establish `h3 : Real.exp (-c' * Real.log x ^ 2) * Real.exp (800 * Real.log x) ≤ 1`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_one_iff.2` to reduce the goal to its premises. Establish `h4 : 800 ≤ c' * Real.log x`. Rewrite `hLc` using `[div_le_iff₀ hc']`.

Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← h2]`. Conclude with `mul_le_mul_of_nonneg_left h1 hδ0`.

Use `_ = 4 * C' * (Real.exp (-c' * Real.log x ^ 2) * Real.exp (800 * Real.log x)) := by`. Rewrite using `[hδ]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 4 * C' * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)`. Use `_ = 4 * C' := by ring`.

Establish `hR` using `gl2a5_R_le hψN he N m₀ (x ^ (ε / 5)) (by positivity) (by`. Introduce `p hp hd hpN`. Break down `hm₀p p hp hd with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Establish `: (p : ℝ) ≤ N` using `by exact_mod_cast hpN`. Use the proof step `linarith)`. Establish `hY : x ^ (ε / 5) * (3 * Real.log x) ≤ 10 * s`. Establish `h1 : x ^ (ε / 5) ≤ x ^ ((1 : ℝ) / 5)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `h2 : Real.log x ≤ x ^ ((3 : ℝ) / 10) / (3 / 10)` using `Real.log_le_rpow_div hx0.le (by norm_num)`.

Establish `h3 : x ^ ((1 : ℝ) / 5) * x ^ ((3 : ℝ) / 10) = s`. Rewrite using `[← Real.rpow_add hx0, hs, Real.sqrt_eq_rpow]`. Evaluate the numerical expressions. Establish `h4 : 3 * Real.log x ≤ 10 * x ^ ((3 : ℝ) / 10)`. Establish `: x ^ ((3 : ℝ) / 10) / (3 / 10) = 10 / 3 * x ^ ((3 : ℝ) / 10)` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Use `set R := ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n with hRdef`. Establish `hR0 : 0 ≤ R` using `Finset.sum_nonneg (fun n _ => hcn0 n)`. Establish `hR16 : R ≤ 16 * s` using `by linarith`.

Establish `hW : ∀ d, ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n ≤ 22 * s`. Introduce `d`. Establish `h1` using `gl2a5_W_le hx0.le N m₀ d`. Establish `h2` using `gl2a5s_le_log he N d`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hW0 : ∀ d, 0 ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n` using `fun d => Finset.sum_nonneg (fun n _ => hcn0 n)`. Establish `hWW` using `mul_le_mul (hW nStar.minFac) (hW (nStar / nStar.minFac)) (hW0 _) (by positivity)`. Establish `hRR : R ^ 2 ≤ (16 * s) ^ 2` using `pow_le_pow_left₀ hR0 hR16 2`. Establish `hxL : x ≤ x * Real.log x` using `le_mul_of_one_le_right hx0.le hL1`. Establish `hfin : (∑ q ∈ PPs, ‖∑ n ∈ Icc 1 N, (cn x n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2) / PPs.card ≤ ∑ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' * |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card|`.

Rewrite using `[← step3, ← step2]`. Conclude with `div_le_div_of_nonneg_right step1 hcard.le`. Use `hfin.trans (step4.trans ?_)` and prove the remaining obligations. Establish `e1 : (16 * s) ^ 2 = 256 * x` using `by rw [mul_pow, sq s, hss]; norm_num`. Establish `e2 : 22 * s * (22 * s) = 484 * x` using `by rw [← hss]; ring`.

Rewrite `hRR` using `[e1]`. Rewrite `hWW` using `[e2]`. Establish `hC'x : 4 * C' ≤ 4 * C' * (x * Real.log x)` using `le_mul_of_one_le_right (by positivity) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem central_sum_estimate : JacobiTwistedMeanSquareBound := by
  intro hψ ε hε0 hε1 C' c' hC' hc'
  refine ⟨max 3 (Real.exp (800 / c')), 4 * C' + 1286, ?_⟩
  intro x hx m₀ PPs κ nStar _ _ hm₀p hne hPP _ _ hκn hμ
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp (800 / c') ≤ x := (le_max_right _ _).trans hx
  have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact he
  have hLc : 800 / c' ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hψN : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ) := by
    intro M
    have := hψ M (Nat.cast_nonneg M)
    rwa [Nat.floor_natCast] at this
  have hcard : (0 : ℝ) < PPs.card := by exact_mod_cast Finset.card_pos.2 hne
  simp only [sqSum]
  set N := ⌊x ^ (400 : ℝ)⌋₊ with hN
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by positivity)
  set δ := C' * Real.exp (-c' * Real.log x ^ 2) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hcn0 : ∀ n, 0 ≤ cn x n := gl2a5_cn_nonneg hx0.le

  have ha : ∀ n, ‖(cn x n : ℂ) * κ n‖ ≤ cn x n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hcn0 n)]
    exact mul_le_of_le_one_right (hcn0 n) (hκn n)
  have step1 := gl2a5_expand (Icc 1 N) PPs (fun n => (cn x n : ℂ) * κ n) (cn x) ha
  have step2 : (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, cn x n * cn x n' *
      |∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)|) / PPs.card =
      ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, cn x n * cn x n' *
        |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card| := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro n' _
    rw [abs_div, Nat.abs_cast, mul_div_assoc]
  have step3 := gl2a5_restrict2 x N
    (fun n n' => |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card|)
  have step4 := gl2a5_comb (primesLeFinset N) (cn x) hcn0 (outPart m₀) Nat.minFac
    (fun n n' => (∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card) δ
    nStar.minFac (nStar / nStar.minFac) (by
      intro n hn n' hn'
      have hn2 := mem_filter.1 hn
      have hn2' := mem_filter.1 hn'
      exact gl2a5_pointwise m₀ nStar hn2.2 hn2'.2 _ δ hδ0 (gl2a5_mean_le_one PPs _)
        (fun h1 h2 => hμ n n' hn2.1 hn2'.1 hn2.2 hn2'.2 h1 h2))
  rw [gl2a5_diag_eq] at step4

  set s := Real.sqrt x with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 hx1
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hLs : Real.log x ≤ 2 * s := gl2a5_log_le_sqrt hx1
  have hD := gl2a5_diag_le hψN hx3 N
  have hsum : ∑ n ∈ primesLeFinset N, cn x n ≤ 2 * x ^ (400 : ℝ) := by
    calc ∑ n ∈ primesLeFinset N, cn x n ≤ ∑ n ∈ Icc 1 N, cn x n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => hcn0 n)
      _ ≤ ∑ n ∈ Icc 1 N, Λ n := Finset.sum_le_sum (fun n _ => gl2a5_cn_le x n)
      _ ≤ 2 * (N : ℝ) := hψN N
      _ ≤ _ := by linarith
  have hsum0 : 0 ≤ ∑ n ∈ primesLeFinset N, cn x n := Finset.sum_nonneg (fun n _ => hcn0 n)
  have hgen : δ * (∑ n ∈ primesLeFinset N, cn x n) ^ 2 ≤ 4 * C' := by
    have h1 : (∑ n ∈ primesLeFinset N, cn x n) ^ 2 ≤ (2 * x ^ (400 : ℝ)) ^ 2 := pow_le_pow_left₀ hsum0 hsum 2
    have h2 : (2 * x ^ (400 : ℝ)) ^ 2 = 4 * Real.exp (800 * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0, mul_pow, ← Real.exp_nat_mul]
      norm_num
      ring_nf
    have h3 : Real.exp (-c' * Real.log x ^ 2) * Real.exp (800 * Real.log x) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      have h4 : 800 ≤ c' * Real.log x := by
        rw [div_le_iff₀ hc'] at hLc; linarith
      nlinarith
    calc δ * (∑ n ∈ primesLeFinset N, cn x n) ^ 2 ≤ δ * (4 * Real.exp (800 * Real.log x)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hδ0
      _ = 4 * C' * (Real.exp (-c' * Real.log x ^ 2) * Real.exp (800 * Real.log x)) := by
          rw [hδ]; ring
      _ ≤ 4 * C' * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 4 * C' := by ring
  have hR := gl2a5_R_le hψN he N m₀ (x ^ (ε / 5)) (by positivity) (by
    intro p hp hd hpN
    rcases hm₀p p hp hd with h | h
    · exact h
    · exfalso
      have : (p : ℝ) ≤ N := by exact_mod_cast hpN
      linarith)
  have hY : x ^ (ε / 5) * (3 * Real.log x) ≤ 10 * s := by
    have h1 : x ^ (ε / 5) ≤ x ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : Real.log x ≤ x ^ ((3 : ℝ) / 10) / (3 / 10) :=
      Real.log_le_rpow_div hx0.le (by norm_num)
    have h3 : x ^ ((1 : ℝ) / 5) * x ^ ((3 : ℝ) / 10) = s := by
      rw [← Real.rpow_add hx0, hs, Real.sqrt_eq_rpow]; norm_num
    have h4 : 3 * Real.log x ≤ 10 * x ^ ((3 : ℝ) / 10) := by
      have : x ^ ((3 : ℝ) / 10) / (3 / 10) = 10 / 3 * x ^ ((3 : ℝ) / 10) := by ring
      linarith
    calc x ^ (ε / 5) * (3 * Real.log x) ≤ x ^ ((1 : ℝ) / 5) * (10 * x ^ ((3 : ℝ) / 10)) :=
          mul_le_mul h1 h4 (by positivity) (by positivity)
      _ = 10 * (x ^ ((1 : ℝ) / 5) * x ^ ((3 : ℝ) / 10)) := by ring
      _ = 10 * s := by rw [h3]
  set R := ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun n _ => hcn0 n)
  have hR16 : R ≤ 16 * s := by linarith
  have hW : ∀ d, ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n ≤ 22 * s := by
    intro d
    have h1 := gl2a5_W_le hx0.le N m₀ d
    have h2 := gl2a5s_le_log he N d
    linarith
  have hW0 : ∀ d, 0 ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n :=
    fun d => Finset.sum_nonneg (fun n _ => hcn0 n)
  have hWW := mul_le_mul (hW nStar.minFac) (hW (nStar / nStar.minFac)) (hW0 _) (by positivity)
  have hRR : R ^ 2 ≤ (16 * s) ^ 2 := pow_le_pow_left₀ hR0 hR16 2
  have hxL : x ≤ x * Real.log x := le_mul_of_one_le_right hx0.le hL1
  have hfin : (∑ q ∈ PPs, ‖∑ n ∈ Icc 1 N, (cn x n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2) /
      PPs.card ≤ ∑ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' *
        |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card| := by
    rw [← step3, ← step2]
    exact div_le_div_of_nonneg_right step1 hcard.le
  refine hfin.trans (step4.trans ?_)
  have e1 : (16 * s) ^ 2 = 256 * x := by rw [mul_pow, sq s, hss]; norm_num
  have e2 : 22 * s * (22 * s) = 484 * x := by rw [← hss]; ring
  rw [e1] at hRR
  rw [e2] at hWW
  have hC'x : 4 * C' ≤ 4 * C' * (x * Real.log x) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  nlinarith

end Formalism.HermitianLattices.GL2PrimeSums
