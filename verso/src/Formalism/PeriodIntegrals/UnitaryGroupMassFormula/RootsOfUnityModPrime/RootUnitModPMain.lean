import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.IdCell

namespace PI.RootUnitModP.W

open NumberField IsDedekindDomain

/- English proof (translation)
Take `⟨c, hc⟩` from `sub_dvd_pow_sub_pow ζ 1 k`. Rewrite `hc` using `[one_pow]`. Rewrite using `[hc]`. Conclude with `P.mul_mem_right c h`.
-/
theorem pow_sub_one_mem {R : Type*} [CommRing R] (P : Ideal R) {ζ : R} (h : ζ - 1 ∈ P) (k : ℕ) :
    ζ ^ k - 1 ∈ P := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ζ 1 k
  rw [one_pow] at hc
  rw [hc]
  exact P.mul_mem_right c h

/- English proof (translation)
Establish `hη' : IsPrimitiveRoot η (q - 1 + 1)` using `by rwa [Nat.sub_add_cancel hq]`. Establish `hprod` using `hη'.prod_one_sub_pow_eq_order`. Establish `hcast : ((q - 1 : ℕ) : R) + 1 = (q : R)`. Rewrite using `[← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hq]`. Rewrite `hprod` using `[hcast]`.

Rewrite using `[← hprod]`. Establish `hmem : (∏ k ∈ Finset.range (q - 1), (1 - η ^ (k + 1))) ∈ ∏ _k ∈ Finset.range (q - 1), P`. Apply `Ideal.prod_mem_prod` to reduce the goal to its premises. Introduce `k _`. Use `pow_sub_one_mem P hP (k + 1)` as an intermediate fact.

Establish `h2 : 1 - η ^ (k + 1) = -(η ^ (k + 1) - 1)` using `by ring`. Rewrite using `[h2]`. Conclude with `P.neg_mem_iff.2 this`. Rewrite `hmem` using `[Finset.prod_const, Finset.card_range]`. Then use the resulting hypothesis.
-/
theorem order_mem_pow {R : Type*} [CommRing R] [IsDomain R] (P : Ideal R) {q : ℕ} (hq : 1 ≤ q)
    {η : R} (hη : IsPrimitiveRoot η q) (hP : η - 1 ∈ P) : (q : R) ∈ P ^ (q - 1) := by
  have hη' : IsPrimitiveRoot η (q - 1 + 1) := by rwa [Nat.sub_add_cancel hq]
  have hprod := hη'.prod_one_sub_pow_eq_order
  have hcast : ((q - 1 : ℕ) : R) + 1 = (q : R) := by
    rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hq]
  rw [hcast] at hprod
  rw [← hprod]
  have hmem : (∏ k ∈ Finset.range (q - 1), (1 - η ^ (k + 1))) ∈
      ∏ _k ∈ Finset.range (q - 1), P := by
    apply Ideal.prod_mem_prod
    intro k _
    have := pow_sub_one_mem P hP (k + 1)
    have h2 : 1 - η ^ (k + 1) = -(η ^ (k + 1) - 1) := by ring
    rw [h2]
    exact P.neg_mem_iff.2 this
  rwa [Finset.prod_const, Finset.card_range] at hmem

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hcop : Nat.Coprime p q` using `(Nat.coprime_primes hp hq).2 hne`. Establish `hZ : IsCoprime (p : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.2 hcop`. Take `⟨a, b, hab⟩` from `hZ`. Establish `h1 : ((a : R) * (p : R) + (b : R) * (q : R)) = 1`.

Use `congrArg (Int.cast : ℤ → R) hab` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Apply `hP` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← h1]`.

Conclude with `P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hqP)`.
-/
theorem prime_eq_of_mem {R : Type*} [CommRing R] (P : Ideal R) (hP : P ≠ ⊤) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpP : (p : R) ∈ P) (hqP : (q : R) ∈ P) : p = q := by
  by_contra hne
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  have hZ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨a, b, hab⟩ := hZ
  have h1 : ((a : R) * (p : R) + (b : R) * (q : R)) = 1 := by
    have := congrArg (Int.cast : ℤ → R) hab
    push_cast at this
    exact this
  apply hP
  rw [Ideal.eq_top_iff_one, ← h1]
  exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hqP)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hfin : IsOfFinOrder ζ` using `isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hζn⟩`. Establish `hm0 : 0 < orderOf ζ` using `hfin.orderOf_pos`. Establish `hm1 : orderOf ζ ≠ 1` using `fun h => hne (orderOf_eq_one_iff.1 h)`. Take `⟨q, hq, hqm⟩` from `Nat.exists_prime_and_dvd hm1`.

Establish `hdvd : orderOf ζ / q ∣ orderOf ζ` using `Nat.div_dvd_of_dvd hqm`. Establish `hne0 : orderOf ζ / q ≠ 0`. Introduce `h`. Break down `Nat.div_eq_zero_iff.1 h with h' | h'` into its components or cases. Conclude with `hq.ne_zero h'`.

Conclude with `absurd (Nat.le_of_dvd hm0 hqm) (not_le.2 h')`. Establish `hη0` using `(IsPrimitiveRoot.orderOf ζ).pow_of_dvd hne0 hdvd`. Rewrite `hη0` using `[Nat.div_div_self hqm hm0.ne']`. Establish `hηP : ζ ^ (orderOf ζ / q) - 1 ∈ P` using `pow_sub_one_mem P hζP _`. Establish `hqmem` using `order_mem_pow P hq.one_le hη0 hηP`.

Establish `hqP : (q : R) ∈ P` using `Ideal.pow_le_self (by have := hq.two_le; omega) hqmem`. Establish `hqg : q = g` using `prime_eq_of_mem P hPp.ne_top hq hg hqP hgP`. Substitute `hqg` using the available equality. Conclude with `hgP2 (Ideal.pow_le_pow_right (by omega) hqmem)`.
-/
theorem root_eq_one {R : Type*} [CommRing R] [IsDomain R] (P : Ideal R) (hPp : P.IsPrime)
    (g : ℕ) (hg : g.Prime) (hg3 : 3 ≤ g) (hgP : (g : R) ∈ P) (hgP2 : (g : R) ∉ P ^ 2)
    (ζ : R) (n : ℕ) (hn : 0 < n) (hζn : ζ ^ n = 1) (hζP : ζ - 1 ∈ P) : ζ = 1 := by
  by_contra hne
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hζn⟩
  have hm0 : 0 < orderOf ζ := hfin.orderOf_pos
  have hm1 : orderOf ζ ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
  have hdvd : orderOf ζ / q ∣ orderOf ζ := Nat.div_dvd_of_dvd hqm
  have hne0 : orderOf ζ / q ≠ 0 := by
    intro h
    rcases Nat.div_eq_zero_iff.1 h with h' | h'
    · exact hq.ne_zero h'
    · exact absurd (Nat.le_of_dvd hm0 hqm) (not_le.2 h')
  have hη0 := (IsPrimitiveRoot.orderOf ζ).pow_of_dvd hne0 hdvd
  rw [Nat.div_div_self hqm hm0.ne'] at hη0
  have hηP : ζ ^ (orderOf ζ / q) - 1 ∈ P := pow_sub_one_mem P hζP _
  have hqmem := order_mem_pow P hq.one_le hη0 hηP
  have hqP : (q : R) ∈ P := Ideal.pow_le_self (by have := hq.two_le; omega) hqmem
  have hqg : q = g := prime_eq_of_mem P hPp.ne_top hq hg hqP hgP
  subst hqg
  exact hgP2 (Ideal.pow_le_pow_right (by omega) hqmem)

/- English proof (translation)
Introduce `g P ζ hg hg3 hgP hgP2 hroot hζP`. Take `⟨n, hn, hζn⟩` from `hroot`. Conclude with `root_eq_one P.asIdeal P.isPrime g hg hg3 hgP hgP2 ζ n hn hζn hζP`.
-/
theorem rootOfUnity_eq_one_mod_prime (E : Type) [Field E] [NumberField E] : Formalism.L2.SG.IdCell.RootModP E := by
  intro g P ζ hg hg3 hgP hgP2 hroot hζP
  obtain ⟨n, hn, hζn⟩ := hroot
  exact root_eq_one P.asIdeal P.isPrime g hg hg3 hgP hgP2 ζ n hn hζn hζP

end PI.RootUnitModP.W
