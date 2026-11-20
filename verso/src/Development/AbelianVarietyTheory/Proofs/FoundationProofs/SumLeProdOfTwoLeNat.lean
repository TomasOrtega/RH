import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Break down `s.eq_empty_or_nonempty with rfl | hs` into its components or cases. Simplify using the standard rewrite rules. Establish `key : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i ∧ 2 ≤ ∏ i ∈ s, f i`. Proceed by induction on `hs using Finset.Nonempty.cons_induction with`. Consider the case `singleton a => simpa using h a (by simp)`.

Consider the case `cons a s ha hs ih`. Rewrite using `[Finset.sum_cons, Finset.prod_cons]`. Take `⟨h1, h2⟩` from `ih (fun i hi => h i (Finset.mem_cons_of_mem hi))`. Establish `h3` using `h a (Finset.mem_cons_self _ _)`. Prove the components needed by the constructor for the conclusion.

Use `Nat.add_le_mul h3 h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use the polynomial consequences of the given equalities and inequalities. Conclude with `key.1`.
-/
theorem sum_le_prod_of_two_le_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, 2 ≤ f i) : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have key : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i ∧ 2 ≤ ∏ i ∈ s, f i := by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simpa using h a (by simp)
    | cons a s ha hs ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      obtain ⟨h1, h2⟩ := ih (fun i hi => h i (Finset.mem_cons_of_mem hi))
      have h3 := h a (Finset.mem_cons_self _ _)
      constructor
      · have := Nat.add_le_mul h3 h2
        omega
      · nlinarith
  exact key.1

/- English proof (translation)
Establish `h1 : 16 * m * a ≤ b * c * a` using `Nat.mul_le_mul_right _ hbc`. Establish `h2 : 16 * m * b ≤ a * c * b` using `Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hc)`. Establish `h3 : 16 * m * c ≤ a * b * c` using `Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hb)`. Establish `h4 : 16 * m * R ≤ a * b * c * R`. Apply `Nat.mul_le_mul_right` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Establish `h5 : a * b * c ≤ a * b * c * R` using `Nat.le_mul_of_pos_right _ hR`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem arith_four (a b c R m : ℕ) (ha : 16 ≤ a) (hb : m ≤ b) (hc : m ≤ c)
    (hbc : 16 * m ≤ b * c) (hR : 1 ≤ R) : 4 * m * (a + b + c + R) ≤ a * b * c * R := by
  have h1 : 16 * m * a ≤ b * c * a := Nat.mul_le_mul_right _ hbc
  have h2 : 16 * m * b ≤ a * c * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hc)
  have h3 : 16 * m * c ≤ a * b * c := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hb)
  have h4 : 16 * m * R ≤ a * b * c * R := by
    apply Nat.mul_le_mul_right
    calc 16 * m ≤ b * c := hbc
      _ ≤ a * (b * c) := Nat.le_mul_of_pos_left _ (by omega)
      _ = a * b * c := by ring
  have h5 : a * b * c ≤ a * b * c * R := Nat.le_mul_of_pos_right _ hR
  nlinarith

/- English proof (translation)
Introduce `n q d hn hq hd hq2 hd2 hqd hmax hdvd`. Use `set f : ℕ → ℕ := fun l => l ^ padicValNat l n with hf`. Establish `hpow : ∀ p k : ℕ, p.Prime → p ^ k ∣ n → p ^ k ≤ f p`. Introduce `p k hp hk`. Use `haveI := Fact.mk hp`.

Conclude with `Nat.pow_le_pow_right hp.pos ((padicValNat_dvd_iff_le hn.ne').1 hk)`. Establish `hge : ∀ p ∈ n.primeFactors, p ≤ f p`. Introduce `p hp`. Use `hpow p 1 (Nat.prime_of_mem_primeFactors hp) (by simpa using Nat.dvd_of_mem_primeFactors hp)` as an intermediate fact. Simplify using `using this`.

Establish `h16 : 2 ^ 4 ∣ n` using `Dvd.dvd.trans ⟨q * d, by ring⟩ hdvd`. Establish `hqn : q ∣ n` using `Dvd.dvd.trans ⟨16 * d, by ring⟩ hdvd`. Establish `hdn : d ∣ n` using `Dvd.dvd.trans ⟨16 * q, by ring⟩ hdvd`. Establish `m2 : 2 ∈ n.primeFactors` using `Nat.mem_primeFactors.2 ⟨Nat.prime_two, Dvd.dvd.trans ⟨8, by norm_num⟩ h16, hn.ne'⟩`. Establish `mq : q ∈ n.primeFactors` using `Nat.mem_primeFactors.2 ⟨hq, hqn, hn.ne'⟩`.

Establish `md : d ∈ n.primeFactors` using `Nat.mem_primeFactors.2 ⟨hd, hdn, hn.ne'⟩`. Establish `ha : 16 ≤ f 2` using `by simpa using hpow 2 4 Nat.prime_two h16`. Establish `hb` using `hge q mq`. Establish `hc` using `hge d md`. Establish `hsub : ({2, q, d} : Finset ℕ) ⊆ n.primeFactors`.

Introduce `x hx`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx`. Apply the tactic sequence `rcases hx with rfl | rfl | rfl <;> assumption`. Establish `hn2 : (2 : ℕ) ∉ ({q, d} : Finset ℕ)`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton]`.

Use linear arithmetic over natural numbers and integers. Establish `hprod : ∏ l ∈ n.primeFactors, f l = n` using `by conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn.ne']`. Rewrite using `[Finsupp.prod, Nat.support_factorization]`. Use `Finset.prod_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]`.

Use `set s := n.primeFactors \ {2, q, d} with hs`. Establish `hs2 : ∀ i ∈ s, 2 ≤ f i` using `fun i hi => (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hi).1).two_le.trans (hge i (Finset.mem_sdiff.1 hi).1)`. Establish `hSP` using `sum_le_prod_of_two_le_nat s f hs2`. Establish `hR : 1 ≤ ∏ i ∈ s, f i` using `Finset.prod_pos (f := f) fun i hi => lt_of_lt_of_le (by norm_num) (hs2 i hi)`. Establish `e1 : n = f 2 * f q * f d * ∏ i ∈ s, f i`.

Rewrite using `[← hprod, ← Finset.prod_sdiff hsub, Finset.prod_insert hn2, Finset.prod_pair hqd]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ l ∈ n.primeFactors, f l = f 2 + f q + f d + ∑ i ∈ s, f i`. Rewrite using `[← Finset.sum_sdiff hsub, Finset.sum_insert hn2, Finset.sum_pair hqd]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hbc : 16 * min q d ≤ f q * f d`. Combine the equalities or inequalities in the displayed calculation. Establish `key` using `arith_four (f 2) (f q) (f d) (∏ i ∈ s, f i) (min q d) ha ((min_le_left _ _).trans hb) ((min_le_right _ _).trans hc) hbc hR`. Rewrite `key` using `[← e1]`. Establish `key2 : (∑ l ∈ n.primeFactors, f l) * (4 * min q d) ≤ n`.

Rewrite using `[e2, mul_comm]`. Conclude with `(Nat.mul_le_mul_left _ (by omega)).trans key`. Establish `hm : 0 < min q d` using `lt_min hq.pos hd.pos`. Rewrite using `[le_div_iff₀ (by positivity), ← Nat.cast_sum]`. Conclude with `key2` after adjusting the coercions.
-/
theorem sum_primePowerParts_le :
    ∀ n q d : ℕ, 0 < n → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → 16 ≤ max q d →
      16 * q * d ∣ n → (∑ l ∈ n.primeFactors, ((l ^ padicValNat l n : ℕ) : ℝ)) ≤
        (n : ℝ) / (4 * ((min q d : ℕ) : ℝ)) := by
  intro n q d hn hq hd hq2 hd2 hqd hmax hdvd
  set f : ℕ → ℕ := fun l => l ^ padicValNat l n with hf
  have hpow : ∀ p k : ℕ, p.Prime → p ^ k ∣ n → p ^ k ≤ f p := by
    intro p k hp hk
    haveI := Fact.mk hp
    exact Nat.pow_le_pow_right hp.pos ((padicValNat_dvd_iff_le hn.ne').1 hk)
  have hge : ∀ p ∈ n.primeFactors, p ≤ f p := by
    intro p hp
    have := hpow p 1 (Nat.prime_of_mem_primeFactors hp)
      (by simpa using Nat.dvd_of_mem_primeFactors hp)
    simpa using this
  have h16 : 2 ^ 4 ∣ n := Dvd.dvd.trans ⟨q * d, by ring⟩ hdvd
  have hqn : q ∣ n := Dvd.dvd.trans ⟨16 * d, by ring⟩ hdvd
  have hdn : d ∣ n := Dvd.dvd.trans ⟨16 * q, by ring⟩ hdvd
  have m2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.prime_two, Dvd.dvd.trans ⟨8, by norm_num⟩ h16, hn.ne'⟩
  have mq : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqn, hn.ne'⟩
  have md : d ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hd, hdn, hn.ne'⟩
  have ha : 16 ≤ f 2 := by simpa using hpow 2 4 Nat.prime_two h16
  have hb := hge q mq
  have hc := hge d md
  have hsub : ({2, q, d} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hn2 : (2 : ℕ) ∉ ({q, d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hprod : ∏ l ∈ n.primeFactors, f l = n := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn.ne']
    rw [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
  set s := n.primeFactors \ {2, q, d} with hs
  have hs2 : ∀ i ∈ s, 2 ≤ f i := fun i hi =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hi).1).two_le.trans
      (hge i (Finset.mem_sdiff.1 hi).1)
  have hSP := sum_le_prod_of_two_le_nat s f hs2
  have hR : 1 ≤ ∏ i ∈ s, f i :=
    Finset.prod_pos (f := f) fun i hi => lt_of_lt_of_le (by norm_num) (hs2 i hi)
  have e1 : n = f 2 * f q * f d * ∏ i ∈ s, f i := by
    rw [← hprod, ← Finset.prod_sdiff hsub, Finset.prod_insert hn2, Finset.prod_pair hqd]
    ring
  have e2 : ∑ l ∈ n.primeFactors, f l = f 2 + f q + f d + ∑ i ∈ s, f i := by
    rw [← Finset.sum_sdiff hsub, Finset.sum_insert hn2, Finset.sum_pair hqd]
    ring
  have hbc : 16 * min q d ≤ f q * f d := by
    calc 16 * min q d ≤ max q d * min q d := Nat.mul_le_mul_right _ hmax
      _ = q * d := max_mul_min q d
      _ ≤ f q * f d := Nat.mul_le_mul hb hc
  have key := arith_four (f 2) (f q) (f d) (∏ i ∈ s, f i) (min q d) ha
    ((min_le_left _ _).trans hb) ((min_le_right _ _).trans hc) hbc hR
  rw [← e1] at key
  have key2 : (∑ l ∈ n.primeFactors, f l) * (4 * min q d) ≤ n := by
    rw [e2, mul_comm]
    exact (Nat.mul_le_mul_left _ (by omega)).trans key
  have hm : 0 < min q d := lt_min hq.pos hd.pos
  rw [le_div_iff₀ (by positivity), ← Nat.cast_sum]
  exact_mod_cast key2

end GlobalTheory.BadShare
