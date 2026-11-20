import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Establish `ha2` using `h a (Finset.mem_insert_self a s)`.

Establish `ih'` using `ih (fun i hi => h i (Finset.mem_insert_of_mem hi))`. Break down `s.eq_empty_or_nonempty with rfl | ⟨b, hb⟩` into its components or cases. Simplify using the standard rewrite rules. Establish `hne : ∏ i ∈ s, f i ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i hi => by`. Use `h i (Finset.mem_insert_of_mem hi)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hP : 2 ≤ ∏ i ∈ s, f i` using `(h b (Finset.mem_insert_of_mem hb)).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Finset.dvd_prod_of_mem f hb))`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_le_prod_of_two_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha2 := h a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rcases s.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · simp
    · have hne : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => by
        have := h i (Finset.mem_insert_of_mem hi)
        omega
      have hP : 2 ≤ ∏ i ∈ s, f i :=
        (h b (Finset.mem_insert_of_mem hb)).trans
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Finset.dvd_prod_of_mem f hb))
      nlinarith

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Use `Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd a (Finset.mem_insert_self a s)) (ih (fun l hl => hp l (Finset.mem_insert_of_mem hl)) (fun l hl => hd l (Finset.mem_insert_of_mem hl)))` and prove the remaining obligations.

Use `Nat.Coprime.prod_right fun l hl => ?_` and prove the remaining obligations. Use `Nat.Coprime.pow _ _ ?_` and prove the remaining obligations. Conclude with `(Nat.coprime_primes (hp a (Finset.mem_insert_self a s)) (hp l (Finset.mem_insert_of_mem hl))).mpr (by rintro rfl; exact ha hl)`.
-/
private theorem prod_prime_pow_dvd_of_forall_dvd (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ)
    (hp : ∀ l ∈ s, l.Prime) (hd : ∀ l ∈ s, l ^ e l ∣ M) : ∏ l ∈ s, l ^ e l ∣ M := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd a (Finset.mem_insert_self a s))
      (ih (fun l hl => hp l (Finset.mem_insert_of_mem hl)) (fun l hl => hd l (Finset.mem_insert_of_mem hl)))
    refine Nat.Coprime.prod_right fun l hl => ?_
    refine Nat.Coprime.pow _ _ ?_
    exact (Nat.coprime_primes (hp a (Finset.mem_insert_self a s)) (hp l (Finset.mem_insert_of_mem hl))).mpr
      (by rintro rfl; exact ha hl)

/- English proof (translation)
Establish `h2 : ∀ l ∈ s, 2 ≤ l ^ e l` using `fun l hl => le_trans (hp l hl).two_le (Nat.le_self_pow (he l hl) l)`. Conclude with `(sum_le_prod_of_two_le s _ h2).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (prod_prime_pow_dvd_of_forall_dvd s e M hp hd))`.
-/
theorem sum_prime_pow_le_of_dvd (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ) (hM : M ≠ 0)
    (hp : ∀ l ∈ s, l.Prime) (he : ∀ l ∈ s, e l ≠ 0) (hd : ∀ l ∈ s, l ^ e l ∣ M) :
    ∑ l ∈ s, l ^ e l ≤ M := by
  have h2 : ∀ l ∈ s, 2 ≤ l ^ e l := fun l hl => le_trans (hp l hl).two_le (Nat.le_self_pow (he l hl) l)
  exact (sum_le_prod_of_two_le s _ h2).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (prod_prime_pow_dvd_of_forall_dvd s e M hp hd))

/- English proof (translation)
Use `Fact.mk hl` as an intermediate fact. Establish `hlg' : ¬ l ∣ g`. Introduce `h`. Establish `h'` using `Nat.dvd_sub h hlg`. Establish `e : g - (g - 1) = 1` using `by omega`.

Rewrite `h'` using `[e]`. Conclude with `hl.one_lt.ne' (Nat.dvd_one.mp h')`. Break down `hl.eq_two_or_odd' with rfl | hodd` into its components or cases. Establish `hx : ¬ (2 : ℤ) ∣ (g : ℤ)` using `by exact_mod_cast hlg'`. Establish `h4' : (4 : ℤ) ∣ (g : ℤ) - 1`.

Use `Int.natCast_dvd_natCast.mpr h4` as an intermediate fact. Rewrite `this` using `[Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one, Nat.cast_ofNat]`. Then use the resulting hypothesis. Establish `key` using `Int.two_pow_sub_pow' d h4' hx`. Rewrite `key` using `[one_pow]`. Establish `e1 : (g : ℤ) ^ d - 1 = ((g ^ d - 1 : ℕ) : ℤ)`.

Rewrite using `[Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (g : ℤ) - 1 = ((g - 1 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_sub (by omega : 1 ≤ g)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : (2 : ℤ) = ((2 : ℕ) : ℤ)` using `rfl`. Rewrite `key` using `[e1, e2, e3, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity]`. Establish `hN : g ^ d - 1 ≠ 0` using `Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hd (by omega))`.

Rewrite using `[← Nat.cast_inj (R := ℕ∞), Nat.cast_add, padicValNat_eq_emultiplicity hN, padicValNat_eq_emultiplicity (by omega : g - 1 ≠ 0), padicValNat_eq_emultiplicity hd]`. Conclude with `key`. Use `padicValNat.pow_sub_pow hodd (by omega : 1 < g) hlg hlg' hd` as an intermediate fact. Rewrite `this` using `[one_pow]`. Then use the resulting hypothesis.
-/
private theorem padicValNat_pow_sub_one_eq_add (g d l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hd : d ≠ 0)
    (hl : l.Prime) (hlg : l ∣ g - 1) :
    padicValNat l (g ^ d - 1) = padicValNat l (g - 1) + padicValNat l d := by
  have := Fact.mk hl
  have hlg' : ¬ l ∣ g := by
    intro h
    have h' := Nat.dvd_sub h hlg
    have e : g - (g - 1) = 1 := by omega
    rw [e] at h'
    exact hl.one_lt.ne' (Nat.dvd_one.mp h')
  rcases hl.eq_two_or_odd' with rfl | hodd
  · have hx : ¬ (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hlg'
    have h4' : (4 : ℤ) ∣ (g : ℤ) - 1 := by
      have := Int.natCast_dvd_natCast.mpr h4
      rwa [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one, Nat.cast_ofNat] at this
    have key := Int.two_pow_sub_pow' d h4' hx
    rw [one_pow] at key
    have e1 : (g : ℤ) ^ d - 1 = ((g ^ d - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
      push_cast
      ring
    have e2 : (g : ℤ) - 1 = ((g - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ g)]
      push_cast
      ring
    have e3 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [e1, e2, e3, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity] at key
    have hN : g ^ d - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hd (by omega))
    rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, padicValNat_eq_emultiplicity hN,
      padicValNat_eq_emultiplicity (by omega : g - 1 ≠ 0), padicValNat_eq_emultiplicity hd]
    exact key
  · have := padicValNat.pow_sub_pow hodd (by omega : 1 < g) hlg hlg' hd
    rwa [one_pow] at this

/- English proof (translation)
Rewrite using `[padicValNat_pow_sub_one_eq_add g d l hg h4 hd hl hlg, pow_add, mul_comm d]`. Conclude with `mul_dvd_mul pow_padicValNat_dvd pow_padicValNat_dvd`.
-/
theorem pow_padicValNat_pow_sub_one_dvd (g d l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hd : d ≠ 0)
    (hl : l.Prime) (hlg : l ∣ g - 1) : l ^ padicValNat l (g ^ d - 1) ∣ d * (g - 1) := by
  rw [padicValNat_pow_sub_one_eq_add g d l hg h4 hd hl hlg, pow_add, mul_comm d]
  exact mul_dvd_mul pow_padicValNat_dvd pow_padicValNat_dvd

/- English proof (translation)
Introduce `g d hg h4 hd`. Use `set N := g ^ d - 1 with hN`. Establish `hd0 : d ≠ 0` using `by omega`. Establish `hg1 : g - 1 ≠ 0` using `by omega`. Establish `hdiv : g - 1 ∣ N` using `by simpa using Nat.sub_dvd_pow_sub_pow g 1 d`.

Establish `hv : ∀ l ∈ N.primeFactors, padicValNat l N ≠ 0`. Introduce `l hl`. Take `⟨hlp, hlN, hN0⟩` from `Nat.mem_primeFactors.mp hl`. Use `Fact.mk hlp` as an intermediate fact. Conclude with `Nat.one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hN0 hlN)`.

Establish `hnat : ∑ l ∈ N.primeFactors, l ^ padicValNat l N ≤ d * (g - 1) + N / (g - 1)`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not N.primeFactors (fun l => l ∣ g - 1)]`. Use `add_le_add ?_ ?_` and prove the remaining obligations. Use `sum_prime_pow_le_of_dvd _ _ _ (mul_ne_zero hd0 hg1) (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1) (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)` and prove the remaining obligations. Take `⟨hl1, hlg⟩` from `Finset.mem_filter.mp hl`.

Conclude with `pow_padicValNat_pow_sub_one_dvd g d l hg h4 hd0 (Nat.mem_primeFactors.mp hl1).1 hlg`. Establish `hQ0 : N / (g - 1) ≠ 0`. Introduce `h0`. Establish `hm` using `Nat.div_mul_cancel hdiv`. Rewrite `hm` using `[h0, zero_mul]`.

Establish `: 1 < g ^ d` using `Nat.one_lt_pow hd0 (by omega)`. Use linear arithmetic over natural numbers and integers. Use `sum_prime_pow_le_of_dvd _ _ _ hQ0 (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1) (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)` and prove the remaining obligations. Take `⟨hl1, hlg⟩` from `Finset.mem_filter.mp hl`. Take `⟨hlp, -, -⟩` from `Nat.mem_primeFactors.mp hl1`.

Establish `hcop : Nat.Coprime (l ^ padicValNat l N) (g - 1)` using `Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hlg)`. Use `hcop.dvd_of_dvd_mul_right ?_` and prove the remaining obligations. Rewrite using `[Nat.div_mul_cancel hdiv]`. Conclude with `pow_padicValNat_dvd`. Establish `hgR : (2 : ℝ) ≤ g` using `by exact_mod_cast hg`.

Establish `hcast_g1 : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega : 1 ≤ g)]`. Simplify using the standard rewrite rules. Establish `hcast_N : ((N : ℕ) : ℝ) = (g : ℝ) ^ d - 1`. Rewrite using `[hN, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]`.

Simplify using the standard rewrite rules. Establish `hcast_Q : ((N / (g - 1) : ℕ) : ℝ) = ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1)`. Rewrite using `[Nat.cast_div hdiv (by rw [hcast_g1]; linarith), hcast_N, hcast_g1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_primePowerPart_pow_sub_one_le :
    ∀ g d : ℕ, 2 ≤ g → 4 ∣ g - 1 → 2 ≤ d → (∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ≤ d * ((g : ℝ) - 1) + ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1) := by
  intro g d hg h4 hd
  set N := g ^ d - 1 with hN
  have hd0 : d ≠ 0 := by omega
  have hg1 : g - 1 ≠ 0 := by omega
  have hdiv : g - 1 ∣ N := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  have hv : ∀ l ∈ N.primeFactors, padicValNat l N ≠ 0 := by
    intro l hl
    obtain ⟨hlp, hlN, hN0⟩ := Nat.mem_primeFactors.mp hl
    have := Fact.mk hlp
    exact Nat.one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hN0 hlN)
  have hnat : ∑ l ∈ N.primeFactors, l ^ padicValNat l N ≤ d * (g - 1) + N / (g - 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (fun l => l ∣ g - 1)]
    refine add_le_add ?_ ?_
    · refine sum_prime_pow_le_of_dvd _ _ _ (mul_ne_zero hd0 hg1)
        (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1)
        (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)
      obtain ⟨hl1, hlg⟩ := Finset.mem_filter.mp hl
      exact pow_padicValNat_pow_sub_one_dvd g d l hg h4 hd0 (Nat.mem_primeFactors.mp hl1).1 hlg
    · have hQ0 : N / (g - 1) ≠ 0 := by
        intro h0
        have hm := Nat.div_mul_cancel hdiv
        rw [h0, zero_mul] at hm
        have : 1 < g ^ d := Nat.one_lt_pow hd0 (by omega)
        omega
      refine sum_prime_pow_le_of_dvd _ _ _ hQ0
        (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1)
        (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)
      obtain ⟨hl1, hlg⟩ := Finset.mem_filter.mp hl
      obtain ⟨hlp, -, -⟩ := Nat.mem_primeFactors.mp hl1
      have hcop : Nat.Coprime (l ^ padicValNat l N) (g - 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hlg)
      refine hcop.dvd_of_dvd_mul_right ?_
      rw [Nat.div_mul_cancel hdiv]
      exact pow_padicValNat_dvd
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hcast_g1 : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ g)]
    simp
  have hcast_N : ((N : ℕ) : ℝ) = (g : ℝ) ^ d - 1 := by
    rw [hN, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    simp
  have hcast_Q : ((N / (g - 1) : ℕ) : ℝ) = ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1) := by
    rw [Nat.cast_div hdiv (by rw [hcast_g1]; linarith), hcast_N, hcast_g1]
  calc (∑ l ∈ N.primeFactors, ((l ^ padicValNat l N : ℕ) : ℝ))
        = ((∑ l ∈ N.primeFactors, l ^ padicValNat l N : ℕ) : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ((d * (g - 1) + N / (g - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = _ := by rw [Nat.cast_add, Nat.cast_mul, hcast_g1, hcast_Q]

end GlobalTheory.BadShare
