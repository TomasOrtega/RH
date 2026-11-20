import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Establish `hq2 : Nat.Coprime 2 q` using `(Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm h2)`. Use `Nat.Coprime.mul_right hq2 (Nat.Coprime.prod_right fun p hp => ?_)` and prove the remaining obligations. Establish `hp'` using `Finset.mem_filter.mp hp`. Establish `h3 : 3 ≤ p` using `(Finset.mem_Icc.mp hp'.1).1`. Conclude with `(Nat.coprime_primes Nat.prime_two hp'.2).mpr (by omega)`.
-/
private theorem oddM_odd (z : ℝ) (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) : Nat.Coprime 2 (oddM z q) := by
  have hq2 : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm h2)
  refine Nat.Coprime.mul_right hq2 (Nat.Coprime.prod_right fun p hp => ?_)
  have hp' := Finset.mem_filter.mp hp
  have h3 : 3 ≤ p := (Finset.mem_Icc.mp hp'.1).1
  exact (Nat.coprime_primes Nat.prime_two hp'.2).mpr (by omega)

/- English proof (translation)
Establish `hM0 : M ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Establish `h16 : Nat.Coprime 16 M`. Use `Nat.Coprime.pow_left 4 h` as an intermediate fact.

Evaluate the numerical expressions using `at this`. Conclude with `this`. Take `⟨c, hc1, hc2⟩` from `Nat.chineseRemainder h16 7 (M - 1)`. Establish `hc3 : c + 1 ≡ 0 [MOD M]`. Use `hc2.add_right 1` as an intermediate fact.

Rewrite `this` using `[Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM0)]`. Conclude with `this.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)`. Establish `hc1' : c % 16 = 7` using `hc1`. Establish `key1 : ∀ d : ℕ, d % 16 = 7 ↔ d ≡ c [MOD 16]`. Introduce `d`.

Unfold `Nat.ModEq`. Rewrite using `[hc1']`. Establish `key2 : ∀ d : ℕ, M ∣ d + 1 ↔ d ≡ c [MOD M]`. Introduce `d`. Rewrite using `[← Nat.modEq_zero_iff_dvd]`.

Prove the components needed by the constructor for the conclusion. Introduce `hd`. Conclude with `Nat.ModEq.add_right_cancel' 1 (hd.trans hc3.symm)`. Introduce `hd`. Conclude with `(hd.add_right 1).trans hc3`.

Establish `hcM : Nat.Coprime c M`. Establish `hdvd : M ∣ c + 1` using `Nat.modEq_zero_iff_dvd.mp hc3`. Establish `hcc : Nat.Coprime c (c + 1)`. Rewrite using `[Nat.coprime_self_add_right]`. Conclude with `Nat.coprime_one_right c`.

Conclude with `Nat.Coprime.coprime_dvd_right hdvd hcc`. Establish `hc16 : Nat.Coprime c 16`. Use `Nat.ModEq.gcd_eq hc1` as an intermediate fact. Unfold `Nat.Coprime`. Rewrite using `[this]`.

Evaluate the numerical expressions. Use `⟨c, Nat.Coprime.mul_right hc16 hcM, fun d => ?_⟩` and prove the remaining obligations. Rewrite using `[key1 d, key2 d]`. Conclude with `Nat.modEq_and_modEq_iff_modEq_mul h16`.
-/
private theorem chineseRemainder_finiteCover (M : ℕ) (h : Nat.Coprime 2 M) : ∃ a : ℕ, a.Coprime (16 * M) ∧
    ∀ d : ℕ, (d % 16 = 7 ∧ M ∣ d + 1) ↔ d % (16 * M) = a % (16 * M) := by
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at h
  have h16 : Nat.Coprime 16 M := by
    have := Nat.Coprime.pow_left 4 h
    norm_num at this
    exact this
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder h16 7 (M - 1)
  have hc3 : c + 1 ≡ 0 [MOD M] := by
    have := hc2.add_right 1
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM0)] at this
    exact this.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
  have hc1' : c % 16 = 7 := hc1
  have key1 : ∀ d : ℕ, d % 16 = 7 ↔ d ≡ c [MOD 16] := by
    intro d
    unfold Nat.ModEq
    rw [hc1']
  have key2 : ∀ d : ℕ, M ∣ d + 1 ↔ d ≡ c [MOD M] := by
    intro d
    rw [← Nat.modEq_zero_iff_dvd]
    constructor
    · intro hd
      exact Nat.ModEq.add_right_cancel' 1 (hd.trans hc3.symm)
    · intro hd
      exact (hd.add_right 1).trans hc3
  have hcM : Nat.Coprime c M := by
    have hdvd : M ∣ c + 1 := Nat.modEq_zero_iff_dvd.mp hc3
    have hcc : Nat.Coprime c (c + 1) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.coprime_one_right c
    exact Nat.Coprime.coprime_dvd_right hdvd hcc
  have hc16 : Nat.Coprime c 16 := by
    have := Nat.ModEq.gcd_eq hc1
    unfold Nat.Coprime
    rw [this]
    norm_num
  refine ⟨c, Nat.Coprime.mul_right hc16 hcM, fun d => ?_⟩
  rw [key1 d, key2 d]
  exact Nat.modEq_and_modEq_iff_modEq_mul h16

/- English proof (translation)
Introduce `z z' q hq h2`. Take `⟨a, ha, hiff⟩` from `chineseRemainder_finiteCover _ (oddM_odd z q hq h2)`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Unfold `primeSetTwoBounds PPset`. Apply `Finset.filter_congr` to reduce the goal to its premises.

Introduce `d _`. Rewrite using `[← hiff d]`. The claim follows by propositional logic.
-/
theorem exists_coprime_primePairSetSecond_eq_PPset :
    ∀ (z z' : ℝ) (q : ℕ), q.Prime → q ≠ 2 → ∃ a₀ : ℕ, a₀.Coprime (16 * oddM z q) ∧
      primeSetTwoBounds z z' q = PPset (16 * oddM z q) a₀ (Real.exp z') := by
  intro z z' q hq h2
  obtain ⟨a, ha, hiff⟩ := chineseRemainder_finiteCover _ (oddM_odd z q hq h2)
  refine ⟨a, ha, ?_⟩
  unfold primeSetTwoBounds PPset
  apply Finset.filter_congr
  intro d _
  rw [← hiff d]
  tauto

end QH
