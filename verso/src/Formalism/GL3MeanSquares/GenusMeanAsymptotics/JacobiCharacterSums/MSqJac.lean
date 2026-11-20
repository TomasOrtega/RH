import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem soutPart_pos (m₀ N : ℕ) : 0 < soutPart m₀ N := by
  unfold soutPart
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem soutPart_squarefree (m₀ N : ℕ) : Squarefree (soutPart m₀ N) := by
  unfold soutPart
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp r hr hpr => ?_) fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1)).mpr hpr

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem soutPart_coprime (m₀ N : ℕ) : (soutPart m₀ N).Coprime m₀ := by
  unfold soutPart
  exact Nat.Coprime.prod_left fun p hp =>
    (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).mpr
      (Finset.mem_filter.mp hp).2.2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem soutPart_odd (m₀ N : ℕ) (h2 : 2 ∣ m₀) : Odd (soutPart m₀ N) := by
  exact Nat.coprime_two_right.mp ((soutPart_coprime m₀ N).coprime_dvd_right h2)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem soutPart_dvd (m₀ N : ℕ) : soutPart m₀ N ∣ N := by
  unfold soutPart
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd N)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem soutPart_le (m₀ N : ℕ) (hN : 0 < N) : soutPart m₀ N ≤ N := by
  exact Nat.le_of_dvd hN (soutPart_dvd m₀ N)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem jacobiSym_prod_left {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ℕ) :
    jacobiSym (∏ i ∈ s, f i) b = ∏ i ∈ s, jacobiSym (f i) b := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, jacobiSym.mul_left, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem jacobiSym_prod_right {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    jacobiSym a (∏ i ∈ s, f i) = ∏ i ∈ s, jacobiSym a (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))
    rw [Finset.prod_cons, Finset.prod_cons,
      jacobiSym.mul_right' _ (hf a (Finset.mem_cons.mpr (Or.inl rfl))) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
theorem recip_sign_congr (p q q' : ℕ) (h4 : q % 4 = q' % 4) :
    ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ (p / 2 * (q' / 2)) := by
  have h : (q / 2) % 2 = (q' / 2) % 2 := by omega
  calc ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ ((p / 2 * (q / 2)) % 2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1) ^ ((p / 2 * (q' / 2)) % 2) := by rw [Nat.mul_mod, h, ← Nat.mul_mod]
    _ = (-1) ^ (p / 2 * (q' / 2)) := (neg_one_pow_eq_pow_mod_two _).symm

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gcd_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ((p : ℤ).gcd (q : ℤ) = 1) ∧ ((q : ℤ).gcd (p : ℤ) = 1) := by
  have h := (Nat.coprime_primes hp hq).mpr hpq.ne
  refine ⟨?_, ?_⟩
  · rw [Int.gcd_natCast_natCast]
    exact h
  · rw [Int.gcd_natCast_natCast]
    exact h.symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem jacobi_prime_in {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : p ∣ m₀) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q = jacobiSym (p : ℤ) q' := by
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  rcases hp.eq_two_or_odd' with rfl | hpo
  · have h8m : q % 8 = q' % 8 := Nat.ModEq.of_dvd h8 hqq
    have hz : (q : ZMod 8) = (q' : ZMod 8) := (ZMod.natCast_eq_natCast_iff' q q' 8).mpr h8m
    simp only [Nat.cast_ofNat]
    rw [jacobiSym.at_two hqo, jacobiSym.at_two hq'o, hz]
  · have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
    have hpm' : q % p = q' % p := Nat.ModEq.of_dvd hpm hqq
    rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o,
      recip_sign_congr p q q' h4, jacobiSym.mod_left (q : ℤ), jacobiSym.mod_left (q' : ℤ),
      ← Int.natCast_mod, ← Int.natCast_mod, hpm']

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem jacobi_prime_out {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : ¬ p ∣ m₀) (hq : q.Prime)
    (hq' : q'.Prime) (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q * jacobiSym (q : ℤ) p = jacobiSym (p : ℤ) q' * jacobiSym (q' : ℤ) p := by
  have hp2 : p ≠ 2 := fun h => hpm (h ▸ dvd_trans (by norm_num) h8)
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hpo := hp.odd_of_ne_two hp2
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
  have s1 : jacobiSym (q : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq hpq).2
  have s2 : jacobiSym (q' : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq' hpq').2
  rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o, mul_assoc, mul_assoc,
    ← sq, ← sq, s1, s2, recip_sign_congr p q q' h4]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem jacobi_class_prod (m₀ N q : ℕ) (hN : 0 < N) :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      ∏ p ∈ N.primeFactors, (jacobiSym (p : ℤ) q ^ (N.factorization p) *
        (if Odd (N.factorization p) ∧ ¬ p ∣ m₀ then jacobiSym (q : ℤ) p else 1)) := by
  have hNfac : (N : ℤ) = ∏ p ∈ N.primeFactors, (p : ℤ) ^ (N.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN.ne']
    rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod]
    simp only [Nat.cast_pow]
  rw [hNfac, jacobiSym_prod_left]
  unfold soutPart
  rw [jacobiSym_prod_right _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero,
    Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [jacobiSym.pow_left]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem jacobi_class_congr {m₀ N q q' : ℕ} (h8 : 8 ∣ m₀) (hN : 0 < N) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hNq : N < q) (hNq' : N < q') :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      jacobiSym (N : ℤ) q' * jacobiSym (q' : ℤ) (soutPart m₀ N) := by
  rw [jacobi_class_prod m₀ N q hN, jacobi_class_prod m₀ N q' hN]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpN : p ≤ N := Nat.le_of_mem_primeFactors hp
  have hpq : p < q := by omega
  have hpq' : p < q' := by omega
  by_cases hpm : p ∣ m₀
  · rw [if_neg (fun h => h.2 hpm), if_neg (fun h => h.2 hpm), mul_one, mul_one,
      jacobi_prime_in h8 hpP hpm hq hq' hqq hpq hpq']
  · have hsq : ∀ r : ℕ, r.Prime → p < r → jacobiSym (p : ℤ) r ^ 2 = 1 := fun r hr hpr =>
      jacobiSym.sq_one (gcd_prime_lt hpP hr hpr).1
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (N.factorization p)
    · have hnodd : ¬ Odd (N.factorization p) := Nat.not_odd_iff_even.mpr ⟨k, by omega⟩
      rw [if_neg (fun h => hnodd h.1), if_neg (fun h => hnodd h.1), mul_one, mul_one, hk, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow]
    · have hodd : Odd (N.factorization p) := ⟨k, hk⟩
      rw [if_pos ⟨hodd, hpm⟩, if_pos ⟨hodd, hpm⟩, hk, pow_succ, pow_succ, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow, one_mul, one_mul]
      exact jacobi_prime_out h8 hpP hpm hq hq' hqq hpq hpq'

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem jacobi_class (m₀ a₀ N : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hN : 0 < N) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ q : ℕ, q.Prime → q % m₀ = a₀ % m₀ → N < q →
      jacobiSym (N : ℤ) q = σ * jacobiSym (q : ℤ) (soutPart m₀ N) := by
  have hcop1 : ∀ q : ℕ, q.Prime → N < q → (N : ℤ).gcd q = 1 := by
    intro q hq hNq
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => absurd (Nat.le_of_dvd hN h) (by omega)).symm
  have hcop2 : ∀ q : ℕ, q.Prime → N < q → (q : ℤ).gcd (soutPart m₀ N) = 1 := by
    intro q hq hNq
    have hle := soutPart_le m₀ N hN
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h =>
      absurd (Nat.le_of_dvd (soutPart_pos m₀ N) h) (by omega)
  by_cases hex : ∃ q₀ : ℕ, q₀.Prime ∧ q₀ % m₀ = a₀ % m₀ ∧ N < q₀
  · obtain ⟨q₀, hq₀, hq₀m, hNq₀⟩ := hex
    refine ⟨jacobiSym (N : ℤ) q₀ * jacobiSym (q₀ : ℤ) (soutPart m₀ N), ?_, fun q hq hqm hNq => ?_⟩
    · rcases jacobiSym.eq_one_or_neg_one (hcop1 q₀ hq₀ hNq₀) with h | h <;>
        rcases jacobiSym.eq_one_or_neg_one (hcop2 q₀ hq₀ hNq₀) with h' | h' <;> simp [h, h']
    · have hc := jacobi_class_congr h8 hN hq hq₀ (hqm.trans hq₀m.symm) hNq hNq₀
      have hsq : jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 = 1 := jacobiSym.sq_one (hcop2 q hq hNq)
      rw [← hc]
      calc jacobiSym (N : ℤ) q = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 := by
            rw [hsq, mul_one]
        _ = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) * jacobiSym (q : ℤ) (soutPart m₀ N) := by
            ring
  · exact ⟨1, Or.inl rfl, fun q hq hqm hNq => absurd ⟨q, hq, hqm, hNq⟩ hex⟩

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
