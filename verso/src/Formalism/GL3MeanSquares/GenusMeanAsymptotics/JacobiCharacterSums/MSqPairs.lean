import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace Pairs

/- English proof (translation)
Simplify using `[Nat.factorization_pow, hp.factorization_self]`.
-/
private lemma factorization_prime_pow_self (p k : ℕ) (hp : p.Prime) : (p ^ k).factorization p = k := by
  simp [Nat.factorization_pow, hp.factorization_self]

/- English proof (translation)
Unfold `soutPart`. Rewrite using `[Nat.primeFactors_prime_pow hk hp, Finset.filter_singleton, factorization_prime_pow_self p k hp]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem soutPart_prime_pow (m₀ p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    soutPart m₀ (p ^ k) = if Odd k ∧ ¬ p ∣ m₀ then p else 1 := by
  unfold soutPart
  rw [Nat.primeFactors_prime_pow hk hp, Finset.filter_singleton, factorization_prime_pow_self p k hp]
  split_ifs <;> simp

/- English proof (translation)
Establish `hfac` using `Nat.factorization_mul_of_coprime h`. Establish `hdisj` using `Nat.Coprime.disjoint_primeFactors h`. Unfold `soutPart`. Rewrite using `[Nat.Coprime.primeFactors_mul h, Finset.filter_union, Finset.prod_union (Finset.disjoint_filter_filter hdisj)]`. Use `congr 1`.

Use `congr 1`. Use `Finset.filter_congr (fun q hq => ?_)` and prove the remaining obligations. Establish `hqb : q ∉ b.primeFactors` using `Finset.disjoint_left.1 hdisj hq`. Establish `h0 : b.factorization q = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `hqb (Nat.support_factorization b ▸ Finsupp.mem_support_iff.2 hne)`. Rewrite using `[hfac, Finsupp.add_apply, h0, add_zero]`. Use `congr 1`. Use `Finset.filter_congr (fun q hq => ?_)` and prove the remaining obligations. Establish `hqa : q ∉ a.primeFactors` using `Finset.disjoint_right.1 hdisj hq`.

Establish `h0 : a.factorization q = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hqa (Nat.support_factorization a ▸ Finsupp.mem_support_iff.2 hne)`. Rewrite using `[hfac, Finsupp.add_apply, h0, zero_add]`.
-/
theorem soutPart_mul_of_coprime (m₀ a b : ℕ) (h : a.Coprime b) :
    soutPart m₀ (a * b) = soutPart m₀ a * soutPart m₀ b := by
  have hfac := Nat.factorization_mul_of_coprime h
  have hdisj := Nat.Coprime.disjoint_primeFactors h
  unfold soutPart
  rw [Nat.Coprime.primeFactors_mul h, Finset.filter_union,
    Finset.prod_union (Finset.disjoint_filter_filter hdisj)]
  congr 1
  · congr 1
    refine Finset.filter_congr (fun q hq => ?_)
    have hqb : q ∉ b.primeFactors := Finset.disjoint_left.1 hdisj hq
    have h0 : b.factorization q = 0 := by
      by_contra hne
      exact hqb (Nat.support_factorization b ▸ Finsupp.mem_support_iff.2 hne)
    rw [hfac, Finsupp.add_apply, h0, add_zero]
  · congr 1
    refine Finset.filter_congr (fun q hq => ?_)
    have hqa : q ∉ a.primeFactors := Finset.disjoint_right.1 hdisj hq
    have h0 : a.factorization q = 0 := by
      by_contra hne
      exact hqa (Nat.support_factorization a ▸ Finsupp.mem_support_iff.2 hne)
    rw [hfac, Finsupp.add_apply, h0, zero_add]

/- English proof (translation)
Take `⟨p, k, hp, hk, rfl⟩` from `(isPrimePow_nat_iff _).1 h`. Establish `hm : (p ^ k).minFac = p` using `hp.pow_minFac hk.ne'`. Use `⟨p, k, hp, hk.ne', rfl, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[hm, factorization_prime_pow_self p k hp]`.
-/
theorem primePow_data {n : ℕ} (h : IsPrimePow n) :
    ∃ p k : ℕ, p.Prime ∧ k ≠ 0 ∧ n = p ^ k ∧ n.minFac = p ∧ n.factorization n.minFac = k := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 h
  have hm : (p ^ k).minFac = p := hp.pow_minFac hk.ne'
  refine ⟨p, k, hp, hk.ne', rfl, hm, ?_⟩
  rw [hm, factorization_prime_pow_self p k hp]

def tPart (m₀ n : ℕ) : ℕ :=
  if Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀ then 1 else n.minFac

/- English proof (translation)
Take `⟨p, k, hp, hk, rfl, hm, -⟩` from `primePow_data h`. Take `⟨q, k', hq, hk', rfl, hm', -⟩` from `primePow_data h'`. Establish `hpq : p = q` using `hm.symm.trans (he.trans hm')`. Substitute `hpq` using the available equality. Rewrite using `[← pow_add, soutPart_prime_pow m₀ p (k + k') hp (by omega), hm]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem soutPart_same {m₀ n n' : ℕ} (h : IsPrimePow n) (h' : IsPrimePow n') (he : n.minFac = n'.minFac) :
    soutPart m₀ (n * n') = 1 ∨ soutPart m₀ (n * n') = n.minFac := by
  obtain ⟨p, k, hp, hk, rfl, hm, -⟩ := primePow_data h
  obtain ⟨q, k', hq, hk', rfl, hm', -⟩ := primePow_data h'
  have hpq : p = q := hm.symm.trans (he.trans hm')
  subst hpq
  rw [← pow_add, soutPart_prime_pow m₀ p (k + k') hp (by omega), hm]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[soutPart_prime_pow m₀ p k hp hk]`. Unfold `tPart`. Rewrite using `[hp.pow_minFac hk, factorization_prime_pow_self p k hp]`. Break down `Nat.even_or_odd k with h1 | h1` into its components or cases. Establish `h1' : ¬ Odd k` using `Nat.not_odd_iff_even.2 h1`.

Simplify using `[h1, h1']`. Establish `h1' : ¬ Even k` using `Nat.not_even_iff_odd.2 h1`. Apply the tactic sequence `by_cases h2 : p ∣ m₀ <;> simp [h1, h1', h2]`.
-/
private lemma tPart_prime_pow_eq_soutPart (m₀ p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    tPart m₀ (p ^ k) = soutPart m₀ (p ^ k) := by
  rw [soutPart_prime_pow m₀ p k hp hk]
  unfold tPart
  rw [hp.pow_minFac hk, factorization_prime_pow_self p k hp]
  rcases Nat.even_or_odd k with h1 | h1
  · have h1' : ¬ Odd k := Nat.not_odd_iff_even.2 h1
    simp [h1, h1']
  · have h1' : ¬ Even k := Nat.not_even_iff_odd.2 h1
    by_cases h2 : p ∣ m₀ <;> simp [h1, h1', h2]

/- English proof (translation)
Take `⟨p, k, hp, hk, rfl, hm, -⟩` from `primePow_data h`. Take `⟨q, k', hq, hk', rfl, hm', -⟩` from `primePow_data h'`. Establish `hpq : p ≠ q` using `fun hpq => he (hm.trans (hpq.trans hm'.symm))`. Establish `hcop : (p ^ k).Coprime (q ^ k')` using `Nat.Coprime.pow k k' ((Nat.coprime_primes hp hq).2 hpq)`. Rewrite using `[soutPart_mul_of_coprime m₀ _ _ hcop, tPart_prime_pow_eq_soutPart m₀ p k hp hk, tPart_prime_pow_eq_soutPart m₀ q k' hq hk']`.
-/
theorem soutPart_diff {m₀ n n' : ℕ} (h : IsPrimePow n) (h' : IsPrimePow n') (he : n.minFac ≠ n'.minFac) :
    soutPart m₀ (n * n') = tPart m₀ n * tPart m₀ n' := by
  obtain ⟨p, k, hp, hk, rfl, hm, -⟩ := primePow_data h
  obtain ⟨q, k', hq, hk', rfl, hm', -⟩ := primePow_data h'
  have hpq : p ≠ q := fun hpq => he (hm.trans (hpq.trans hm'.symm))
  have hcop : (p ^ k).Coprime (q ^ k') := Nat.Coprime.pow k k' ((Nat.coprime_primes hp hq).2 hpq)
  rw [soutPart_mul_of_coprime m₀ _ _ hcop, tPart_prime_pow_eq_soutPart m₀ p k hp hk, tPart_prime_pow_eq_soutPart m₀ q k' hq hk']

def aW (c : ℕ → ℝ) (p n : ℕ) : ℝ := if IsPrimePow n ∧ n.minFac = p then c n else 0

def gW (c : ℕ → ℝ) (m₀ n : ℕ) : ℝ :=
  if IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀) then c n else 0

/- English proof (translation)
Simplify using `only [sP, aW, Finset.sum_filter]`.
-/
theorem primePowerSum_eq_sum_Icc (c : ℕ → ℝ) (N p : ℕ) : sP c N p = ∑ n ∈ Icc 1 N, aW c p n := by
  simp only [sP, aW, Finset.sum_filter]

/- English proof (translation)
Simplify using `only [RR, gW, Finset.sum_filter]`.
-/
theorem RR_eq (c : ℕ → ℝ) (m₀ N : ℕ) : RR c m₀ N = ∑ n ∈ Icc 1 N, gW c m₀ n := by
  simp only [RR, gW, Finset.sum_filter]

/- English proof (translation)
Unfold `aW`. Use `split_ifs`. Conclude with `hc n`. Conclude with `le_refl 0`.
-/
theorem aW_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (p n : ℕ) : 0 ≤ aW c p n := by
  unfold aW
  split_ifs
  · exact hc n
  · exact le_refl 0

/- English proof (translation)
Unfold `gW`. Use `split_ifs`. Conclude with `hc n`. Conclude with `le_refl 0`.
-/
theorem gW_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (m₀ n : ℕ) : 0 ≤ gW c m₀ n := by
  unfold gW
  split_ifs
  · exact hc n
  · exact le_refl 0

/- English proof (translation)
Conclude with `Finset.sum_nonneg (fun n _ => hc n)`.
-/
theorem sP_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (N p : ℕ) : 0 ≤ sP c N p := by
  exact Finset.sum_nonneg (fun n _ => hc n)

/- English proof (translation)
Conclude with `Finset.sum_nonneg (fun n _ => hc n)`.
-/
theorem RR_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (m₀ N : ℕ) : 0 ≤ RR c m₀ N := by
  exact Finset.sum_nonneg (fun n _ => hc n)

/- English proof (translation)
Unfold `aW`. Rewrite using `[if_pos ⟨h, rfl⟩]`.
-/
theorem aW_self {c : ℕ → ℝ} {n : ℕ} (h : IsPrimePow n) : aW c n.minFac n = c n := by
  unfold aW
  rw [if_pos ⟨h, rfl⟩]

/- English proof (translation)
Establish `hcond : Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀`. Unfold `tPart at ht`. Use `split_ifs at ht with h1`. Conclude with `h1`. Conclude with `absurd ht (Nat.minFac_prime h.ne_one).one_lt.ne'`.

Unfold `gW`. Rewrite using `[if_pos ⟨h, hcond⟩]`.
-/
theorem gW_eq_of_tPart_eq_one {c : ℕ → ℝ} {m₀ n : ℕ} (h : IsPrimePow n) (ht : tPart m₀ n = 1) : gW c m₀ n = c n := by
  have hcond : Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀ := by
    unfold tPart at ht
    split_ifs at ht with h1
    · exact h1
    · exact absurd ht (Nat.minFac_prime h.ne_one).one_lt.ne'
  unfold gW
  rw [if_pos ⟨h, hcond⟩]

/- English proof (translation)
Unfold `tPart`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem tPart_cases (m₀ n : ℕ) : tPart m₀ n = 1 ∨ tPart m₀ n = n.minFac := by
  unfold tPart
  split_ifs <;> simp

/- English proof (translation)
The claim follows from `Nat.minFac_prime h.ne_one`.
-/
theorem minFac_prime_of_pp {n : ℕ} (h : IsPrimePow n) : n.minFac.Prime := Nat.minFac_prime h.ne_one

/- English proof (translation)
Rewrite using `[Finset.sum_mul_sum]`.
-/
theorem dbl_sum (s : Finset ℕ) (f g : ℕ → ℝ) :
    ∑ n ∈ s, ∑ n' ∈ s, f n * g n' = (∑ n ∈ s, f n) * ∑ n ∈ s, g n := by
  rw [Finset.sum_mul_sum]

/- English proof (translation)
Establish `hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤ aW c r n * aW c r n' + aW c r n * gW c m₀ n' + gW c m₀ n * aW c r n'`. Introduce `n n'`. Establish `q1` using `mul_nonneg (aW_nonneg hc r n) (aW_nonneg hc r n')`. Establish `q2` using `mul_nonneg (aW_nonneg hc r n) (gW_nonneg hc m₀ n')`. Establish `q3` using `mul_nonneg (gW_nonneg hc m₀ n) (aW_nonneg hc r n')`.

Use `split_ifs with hs`. Use `swap`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hcn : c n = 0`. Rewrite using `[hcn, zero_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hcn' : c n' = 0`. Rewrite using `[hcn', mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn` using `hpp n hcn`.

Establish `hn'` using `hpp n' hcn'`. Distinguish the cases in `he : n.minFac = n'.minFac`. Break down `soutPart_same (m₀ := m₀) hn hn' he with h1 | h1` into its components or cases. Conclude with `absurd (hs.symm.trans h1) hr.one_lt.ne'`. Establish `hnr : n.minFac = r` using `h1.symm.trans hs`.

Establish `hnr' : n'.minFac = r` using `he.symm.trans hnr`. Establish `e1 : aW c r n = c n` using `by unfold aW; rw [if_pos ⟨hn, hnr⟩]`. Establish `e2 : aW c r n' = c n'` using `by unfold aW; rw [if_pos ⟨hn', hnr'⟩]`. Rewrite using `[e1, e2]`. Use `mul_nonneg (hc n) (gW_nonneg hc m₀ n')` as an intermediate fact.

Use `mul_nonneg (gW_nonneg hc m₀ n) (hc n')` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd` using `soutPart_diff (m₀ := m₀) hn hn' he`. Rewrite `hd` using `[hs]`. Establish `p1` using `Nat.minFac_prime hn.ne_one`.

Establish `p2` using `Nat.minFac_prime hn'.ne_one`. Apply the tactic sequence `rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>`. Rewrite `hd` using `[t1, t2]`. Conclude with `absurd (hd.trans (one_mul 1)) hr.one_lt.ne'`. Establish `e1 : gW c m₀ n = c n` using `gW_eq_of_tPart_eq_one hn t1`.

Establish `e2 : aW c r n' = c n'`. Unfold `aW; rw [if_pos ⟨hn', by rw [hd, one_mul]⟩]`. Rewrite using `[e1, e2]`. Use `mul_nonneg (aW_nonneg hc r n) (hc n')` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e1 : aW c r n = c n`. Unfold `aW; rw [if_pos ⟨hn, by rw [hd, mul_one]⟩]`. Establish `e2 : gW c m₀ n' = c n'` using `gW_eq_of_tPart_eq_one hn' t2`. Rewrite using `[e1, e2]`. Use `mul_nonneg (hc n) (aW_nonneg hc r n')` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. It suffices to derive a contradiction. Rewrite `hr` using `[hd]`. Break down `Nat.prime_mul_iff.1 hr with ⟨-, h⟩ | ⟨-, h⟩` into its components or cases. Conclude with `p2.one_lt.ne' h`.

Conclude with `p1.one_lt.ne' h`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_add_distrib, dbl_sum, primePowerSum_eq_sum_Icc, RR_eq]`.
-/
theorem pairs_r_prime (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ)
    (hr : r.Prime) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      sP c N r * sP c N r + sP c N r * RR c m₀ N + RR c m₀ N * sP c N r := by
  have hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      aW c r n * aW c r n' + aW c r n * gW c m₀ n' + gW c m₀ n * aW c r n' := by
    intro n n'
    have q1 := mul_nonneg (aW_nonneg hc r n) (aW_nonneg hc r n')
    have q2 := mul_nonneg (aW_nonneg hc r n) (gW_nonneg hc m₀ n')
    have q3 := mul_nonneg (gW_nonneg hc m₀ n) (aW_nonneg hc r n')
    split_ifs with hs
    swap
    · linarith
    by_cases hcn : c n = 0
    · rw [hcn, zero_mul]; linarith
    by_cases hcn' : c n' = 0
    · rw [hcn', mul_zero]; linarith
    have hn := hpp n hcn
    have hn' := hpp n' hcn'
    by_cases he : n.minFac = n'.minFac
    · rcases soutPart_same (m₀ := m₀) hn hn' he with h1 | h1
      · exact absurd (hs.symm.trans h1) hr.one_lt.ne'
      · have hnr : n.minFac = r := h1.symm.trans hs
        have hnr' : n'.minFac = r := he.symm.trans hnr
        have e1 : aW c r n = c n := by unfold aW; rw [if_pos ⟨hn, hnr⟩]
        have e2 : aW c r n' = c n' := by unfold aW; rw [if_pos ⟨hn', hnr'⟩]
        rw [e1, e2]
        have := mul_nonneg (hc n) (gW_nonneg hc m₀ n')
        have := mul_nonneg (gW_nonneg hc m₀ n) (hc n')
        linarith
    · have hd := soutPart_diff (m₀ := m₀) hn hn' he
      rw [hs] at hd
      have p1 := Nat.minFac_prime hn.ne_one
      have p2 := Nat.minFac_prime hn'.ne_one
      rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>
        rw [t1, t2] at hd
      · exact absurd (hd.trans (one_mul 1)) hr.one_lt.ne'
      · have e1 : gW c m₀ n = c n := gW_eq_of_tPart_eq_one hn t1
        have e2 : aW c r n' = c n' := by
          unfold aW; rw [if_pos ⟨hn', by rw [hd, one_mul]⟩]
        rw [e1, e2]
        have := mul_nonneg (aW_nonneg hc r n) (hc n')
        linarith
      · have e1 : aW c r n = c n := by
          unfold aW; rw [if_pos ⟨hn, by rw [hd, mul_one]⟩]
        have e2 : gW c m₀ n' = c n' := gW_eq_of_tPart_eq_one hn' t2
        rw [e1, e2]
        have := mul_nonneg (hc n) (aW_nonneg hc r n')
        linarith
      · exfalso
        rw [hd] at hr
        rcases Nat.prime_mul_iff.1 hr with ⟨-, h⟩ | ⟨-, h⟩
        · exact p2.one_lt.ne' h
        · exact p1.one_lt.ne' h
  calc (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0)
      ≤ ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N,
          (aW c r n * aW c r n' + aW c r n * gW c m₀ n' + gW c m₀ n * aW c r n') :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun n' _ => hpt n n'))
    _ = sP c N r * sP c N r + sP c N r * RR c m₀ N + RR c m₀ N * sP c N r := by
        simp only [Finset.sum_add_distrib, dbl_sum, primePowerSum_eq_sum_Icc, RR_eq]

/- English proof (translation)
Establish `hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤ aW c r.minFac n * aW c (r / r.minFac) n' + aW c (r / r.minFac) n * aW c r.minFac n'`. Introduce `n n'`. Establish `q1` using `mul_nonneg (aW_nonneg hc r.minFac n) (aW_nonneg hc (r / r.minFac) n')`. Establish `q2` using `mul_nonneg (aW_nonneg hc (r / r.minFac) n) (aW_nonneg hc r.minFac n')`. Use `split_ifs with hs`.

Use `swap`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hcn : c n = 0`. Rewrite using `[hcn, zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `hcn' : c n' = 0`. Rewrite using `[hcn', mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn` using `hpp n hcn`. Establish `hn'` using `hpp n' hcn'`.

Establish `p1` using `Nat.minFac_prime hn.ne_one`. Establish `p2` using `Nat.minFac_prime hn'.ne_one`. Distinguish the cases in `he : n.minFac = n'.minFac`. It suffices to derive a contradiction. Break down `soutPart_same (m₀ := m₀) hn hn' he with h1 | h1` into its components or cases.

Conclude with `hr.ne' (hs.symm.trans h1)`. Conclude with `hrp (by rw [← hs, h1]; exact p1)`. Establish `hd` using `soutPart_diff (m₀ := m₀) hn hn' he`. Rewrite `hd` using `[hs]`. Apply the tactic sequence `rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>`.

Rewrite `hd` using `[t1, t2]`. Conclude with `absurd (hd.trans (one_mul 1)) hr.ne'`. Conclude with `absurd (by rw [hd, one_mul]; exact p2) hrp`. Conclude with `absurd (by rw [hd, mul_one]; exact p1) hrp`. Establish `hmf : r.minFac = n.minFac ∨ r.minFac = n'.minFac`.

Establish `hpr` using `Nat.minFac_prime (show r ≠ 1 by omega)`. Establish `hdvd : r.minFac ∣ n.minFac * n'.minFac` using `by rw [← hd]; exact Nat.minFac_dvd r`. Break down `(Nat.Prime.dvd_mul hpr).1 hdvd with h | h` into its components or cases. Conclude with `Or.inl ((Nat.prime_dvd_prime_iff_eq hpr p1).1 h)`. Conclude with `Or.inr ((Nat.prime_dvd_prime_iff_eq hpr p2).1 h)`.

Establish `ha : aW c n.minFac n = c n` using `aW_self hn`. Establish `hb : aW c n'.minFac n' = c n'` using `aW_self hn'`. Break down `hmf with h | h` into its components or cases. Establish `hq : r / r.minFac = n'.minFac` using `by rw [h, hd, Nat.mul_div_cancel_left _ p1.pos]`. Rewrite using `[hq, h, ha, hb]`.

Use `mul_nonneg (aW_nonneg hc n'.minFac n) (aW_nonneg hc n.minFac n')` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : r / r.minFac = n.minFac` using `by rw [h, hd, Nat.mul_div_cancel _ p2.pos]`. Rewrite using `[hq, h, ha, hb]`. Use `mul_nonneg (aW_nonneg hc n'.minFac n) (aW_nonneg hc n.minFac n')` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_add_distrib, dbl_sum, primePowerSum_eq_sum_Icc]`.
-/
theorem pairs_r_not_prime (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ)
    (hr : 1 < r) (hrp : ¬ r.Prime) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      sP c N r.minFac * sP c N (r / r.minFac) + sP c N (r / r.minFac) * sP c N r.minFac := by
  have hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      aW c r.minFac n * aW c (r / r.minFac) n' + aW c (r / r.minFac) n * aW c r.minFac n' := by
    intro n n'
    have q1 := mul_nonneg (aW_nonneg hc r.minFac n) (aW_nonneg hc (r / r.minFac) n')
    have q2 := mul_nonneg (aW_nonneg hc (r / r.minFac) n) (aW_nonneg hc r.minFac n')
    split_ifs with hs
    swap
    · linarith
    by_cases hcn : c n = 0
    · rw [hcn, zero_mul]; linarith
    by_cases hcn' : c n' = 0
    · rw [hcn', mul_zero]; linarith
    have hn := hpp n hcn
    have hn' := hpp n' hcn'
    have p1 := Nat.minFac_prime hn.ne_one
    have p2 := Nat.minFac_prime hn'.ne_one
    by_cases he : n.minFac = n'.minFac
    · exfalso
      rcases soutPart_same (m₀ := m₀) hn hn' he with h1 | h1
      · exact hr.ne' (hs.symm.trans h1)
      · exact hrp (by rw [← hs, h1]; exact p1)
    · have hd := soutPart_diff (m₀ := m₀) hn hn' he
      rw [hs] at hd
      rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>
        rw [t1, t2] at hd
      · exact absurd (hd.trans (one_mul 1)) hr.ne'
      · exact absurd (by rw [hd, one_mul]; exact p2) hrp
      · exact absurd (by rw [hd, mul_one]; exact p1) hrp
      · have hmf : r.minFac = n.minFac ∨ r.minFac = n'.minFac := by
          have hpr := Nat.minFac_prime (show r ≠ 1 by omega)
          have hdvd : r.minFac ∣ n.minFac * n'.minFac := by rw [← hd]; exact Nat.minFac_dvd r
          rcases (Nat.Prime.dvd_mul hpr).1 hdvd with h | h
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpr p1).1 h)
          · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpr p2).1 h)
        have ha : aW c n.minFac n = c n := aW_self hn
        have hb : aW c n'.minFac n' = c n' := aW_self hn'
        rcases hmf with h | h
        · have hq : r / r.minFac = n'.minFac := by rw [h, hd, Nat.mul_div_cancel_left _ p1.pos]
          rw [hq, h, ha, hb]
          have := mul_nonneg (aW_nonneg hc n'.minFac n) (aW_nonneg hc n.minFac n')
          linarith
        · have hq : r / r.minFac = n.minFac := by rw [h, hd, Nat.mul_div_cancel _ p2.pos]
          rw [hq, h, ha, hb]
          have := mul_nonneg (aW_nonneg hc n'.minFac n) (aW_nonneg hc n.minFac n')
          linarith
  calc (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0)
      ≤ ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N,
          (aW c r.minFac n * aW c (r / r.minFac) n' + aW c (r / r.minFac) n * aW c r.minFac n') :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun n' _ => hpt n n'))
    _ = sP c N r.minFac * sP c N (r / r.minFac) + sP c N (r / r.minFac) * sP c N r.minFac := by
        simp only [Finset.sum_add_distrib, dbl_sum, primePowerSum_eq_sum_Icc]

end Pairs

open Pairs

/- English proof (translation)
Use `set P := (Icc 1 N).filter Nat.Prime with hPdef`. Establish `hpt : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N, (if soutPart m₀ (n * n') = 1 then c n * c n' else 0) ≤ ∑ p ∈ P, aW c p n * aW c p n' + gW c m₀ n * gW c m₀ n'`. Introduce `n hnN n' _`. Establish `h0 : 0 ≤ ∑ p ∈ P, aW c p n * aW c p n'` using `Finset.sum_nonneg (fun p _ => mul_nonneg (aW_nonneg hc _ _) (aW_nonneg hc _ _))`. Establish `h0' : 0 ≤ gW c m₀ n * gW c m₀ n'` using `mul_nonneg (gW_nonneg hc _ _) (gW_nonneg hc _ _)`.

Use `split_ifs with hs`. Use `swap`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hcn : c n = 0`. Rewrite using `[hcn, zero_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hcn' : c n' = 0`. Rewrite using `[hcn', mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn` using `hpp n hcn`.

Establish `hn'` using `hpp n' hcn'`. Establish `p1` using `Nat.minFac_prime hn.ne_one`. Distinguish the cases in `he : n.minFac = n'.minFac`. Establish `hmem : n.minFac ∈ P`. Rewrite using `[hPdef, Finset.mem_filter, Finset.mem_Icc]`.

Rewrite `hnN` using `[Finset.mem_Icc]`. Conclude with `⟨⟨p1.one_lt.le, le_trans (Nat.minFac_le (by omega)) hnN.2⟩, p1⟩`. Establish `hsingle` using `Finset.single_le_sum (f := fun p => aW c p n * aW c p n') (fun p _ => mul_nonneg (aW_nonneg hc _ _) (aW_nonneg hc _ _)) hmem`. Establish `ha : aW c n.minFac n = c n` using `aW_self hn`. Establish `hb : aW c n.minFac n' = c n'` using `by rw [he]; exact aW_self hn'`.

Simplify using `only [ha, hb] at hsingle`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd` using `soutPart_diff (m₀ := m₀) hn hn' he`. Rewrite `hd` using `[hs]`. Establish `t1 : tPart m₀ n = 1` using `Nat.eq_one_of_mul_eq_one_right hd.symm`.

Establish `t2 : tPart m₀ n' = 1` using `Nat.eq_one_of_mul_eq_one_left hd.symm`. Rewrite using `[gW_eq_of_tPart_eq_one hn t1, gW_eq_of_tPart_eq_one hn' t2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, aW c p n * aW c p n' = ∑ p ∈ P, sP c N p ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun n _ => Finset.sum_add_distrib)`. Use `_ = (∑ p ∈ P, sP c N p ^ 2) + RR c m₀ N ^ 2 := by`. Rewrite using `[e, dbl_sum, ← RR_eq, sq]`.
-/
theorem pairs_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = 1 then c n * c n' else 0) ≤
      (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) + RR c m₀ N ^ 2 := by
  set P := (Icc 1 N).filter Nat.Prime with hPdef
  have hpt : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N, (if soutPart m₀ (n * n') = 1 then c n * c n' else 0) ≤
      ∑ p ∈ P, aW c p n * aW c p n' + gW c m₀ n * gW c m₀ n' := by
    intro n hnN n' _
    have h0 : 0 ≤ ∑ p ∈ P, aW c p n * aW c p n' :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (aW_nonneg hc _ _) (aW_nonneg hc _ _))
    have h0' : 0 ≤ gW c m₀ n * gW c m₀ n' := mul_nonneg (gW_nonneg hc _ _) (gW_nonneg hc _ _)
    split_ifs with hs
    swap
    · linarith
    by_cases hcn : c n = 0
    · rw [hcn, zero_mul]; linarith
    by_cases hcn' : c n' = 0
    · rw [hcn', mul_zero]; linarith
    have hn := hpp n hcn
    have hn' := hpp n' hcn'
    have p1 := Nat.minFac_prime hn.ne_one
    by_cases he : n.minFac = n'.minFac
    · have hmem : n.minFac ∈ P := by
        rw [hPdef, Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_Icc] at hnN
        exact ⟨⟨p1.one_lt.le, le_trans (Nat.minFac_le (by omega)) hnN.2⟩, p1⟩
      have hsingle := Finset.single_le_sum (f := fun p => aW c p n * aW c p n')
        (fun p _ => mul_nonneg (aW_nonneg hc _ _) (aW_nonneg hc _ _)) hmem
      have ha : aW c n.minFac n = c n := aW_self hn
      have hb : aW c n.minFac n' = c n' := by rw [he]; exact aW_self hn'
      simp only [ha, hb] at hsingle
      linarith
    · have hd := soutPart_diff (m₀ := m₀) hn hn' he
      rw [hs] at hd
      have t1 : tPart m₀ n = 1 := Nat.eq_one_of_mul_eq_one_right hd.symm
      have t2 : tPart m₀ n' = 1 := Nat.eq_one_of_mul_eq_one_left hd.symm
      rw [gW_eq_of_tPart_eq_one hn t1, gW_eq_of_tPart_eq_one hn' t2]
      linarith
  have e : ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, aW c p n * aW c p n' = ∑ p ∈ P, sP c N p ^ 2 := by
    calc _ = ∑ n ∈ Icc 1 N, ∑ p ∈ P, ∑ n' ∈ Icc 1 N, aW c p n * aW c p n' :=
          Finset.sum_congr rfl (fun n _ => Finset.sum_comm)
      _ = ∑ p ∈ P, ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, aW c p n * aW c p n' := Finset.sum_comm
      _ = ∑ p ∈ P, sP c N p ^ 2 := Finset.sum_congr rfl (fun p _ => by rw [dbl_sum, ← primePowerSum_eq_sum_Icc, sq])
  calc (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = 1 then c n * c n' else 0)
      ≤ ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, (∑ p ∈ P, aW c p n * aW c p n' + gW c m₀ n * gW c m₀ n') :=
        Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun n' hn' => hpt n hn n' hn'))
    _ = ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, aW c p n * aW c p n' +
          ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, gW c m₀ n * gW c m₀ n' := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => Finset.sum_add_distrib)
    _ = (∑ p ∈ P, sP c N p ^ 2) + RR c m₀ N ^ 2 := by
        rw [e, dbl_sum, ← RR_eq, sq]

/- English proof (translation)
Establish `hB0 : 0 ≤ B` using `le_trans (sP_nonneg hc N 0) (hB 0)`. Establish `hR` using `RR_nonneg hc m₀ N`. Distinguish the cases in `hrp : r.Prime`. Use `le_trans (pairs_r_prime c hc hpp m₀ N r hrp) ?_` and prove the remaining obligations. Establish `h1` using `sP_nonneg hc N r`.

Establish `h2` using `hB r`. Use polynomial arithmetic with `[mul_le_mul h2 h2 h1 hB0, mul_le_mul_of_nonneg_right h2 hR, mul_nonneg hB0 hB0]`. Use `le_trans (pairs_r_not_prime c hc hpp m₀ N r hr hrp) ?_` and prove the remaining obligations. Establish `a1` using `sP_nonneg hc N r.minFac`. Establish `a2` using `sP_nonneg hc N (r / r.minFac)`.

Establish `b1` using `hB r.minFac`. Establish `b2` using `hB (r / r.minFac)`. Use polynomial arithmetic with `[mul_le_mul b1 b2 a2 hB0, mul_le_mul b2 b1 a1 hB0, mul_nonneg hB0 hR]`.
-/
theorem pairs_r (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ) (hr : 1 < r)
    (B : ℝ) (hB : ∀ p, sP c N p ≤ B) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      2 * B ^ 2 + 2 * B * RR c m₀ N := by
  have hB0 : 0 ≤ B := le_trans (sP_nonneg hc N 0) (hB 0)
  have hR := RR_nonneg hc m₀ N
  by_cases hrp : r.Prime
  · refine le_trans (pairs_r_prime c hc hpp m₀ N r hrp) ?_
    have h1 := sP_nonneg hc N r
    have h2 := hB r
    nlinarith [mul_le_mul h2 h2 h1 hB0, mul_le_mul_of_nonneg_right h2 hR, mul_nonneg hB0 hB0]
  · refine le_trans (pairs_r_not_prime c hc hpp m₀ N r hr hrp) ?_
    have a1 := sP_nonneg hc N r.minFac
    have a2 := sP_nonneg hc N (r / r.minFac)
    have b1 := hB r.minFac
    have b2 := hB (r / r.minFac)
    nlinarith [mul_le_mul b1 b2 a2 hB0, mul_le_mul b2 b1 a1 hB0, mul_nonneg hB0 hR]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
