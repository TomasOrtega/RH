import Formalism.GrowthSums.StatementA

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

/- English proof (translation)
Use `revert hpos hv`. Proceed by induction on `hS using Finset.Nonempty.cons_induction with`. Consider the case `singleton a`. Introduce `_ hv`. Simplify using `using hv a (Finset.mem_singleton_self a)`.

Consider the case `cons a T haT hT ih`. Introduce `hpos hv`. Establish `h1 : s ≤ padicValRat p (F a)` using `hv a (Finset.mem_cons.2 (Or.inl rfl))`. Establish `h2 : s ≤ padicValRat p (∑ i ∈ T, F i)` using `ih (fun i hi => hpos i (Finset.mem_cons.2 (Or.inr hi))) (fun i hi => hv i (Finset.mem_cons.2 (Or.inr hi)))`. Establish `hpa : 0 < F a` using `hpos a (Finset.mem_cons.2 (Or.inl rfl))`.

Establish `hpT : 0 < ∑ i ∈ T, F i` using `Finset.sum_pos (fun i hi => hpos i (Finset.mem_cons.2 (Or.inr hi))) hT`. Establish `hne : F a + ∑ i ∈ T, F i ≠ 0` using `(add_pos hpa hpT).ne'`. Rewrite using `[Finset.sum_cons]`. Conclude with `le_trans (le_min h1 h2) (padicValRat.min_le_padicValRat_add hne)`.
-/
theorem le_padicValRat_sum_of_pos {p : ℕ} [Fact p.Prime] (s : ℤ) {F : ℕ → ℚ} {S : Finset ℕ}
    (hS : S.Nonempty) (hpos : ∀ i ∈ S, 0 < F i) (hv : ∀ i ∈ S, s ≤ padicValRat p (F i)) :
    s ≤ padicValRat p (∑ i ∈ S, F i) := by
  revert hpos hv
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro _ hv
    simpa using hv a (Finset.mem_singleton_self a)
  | cons a T haT hT ih =>
    intro hpos hv
    have h1 : s ≤ padicValRat p (F a) := hv a (Finset.mem_cons.2 (Or.inl rfl))
    have h2 : s ≤ padicValRat p (∑ i ∈ T, F i) :=
      ih (fun i hi => hpos i (Finset.mem_cons.2 (Or.inr hi)))
        (fun i hi => hv i (Finset.mem_cons.2 (Or.inr hi)))
    have hpa : 0 < F a := hpos a (Finset.mem_cons.2 (Or.inl rfl))
    have hpT : 0 < ∑ i ∈ T, F i :=
      Finset.sum_pos (fun i hi => hpos i (Finset.mem_cons.2 (Or.inr hi))) hT
    have hne : F a + ∑ i ∈ T, F i ≠ 0 := (add_pos hpa hpT).ne'
    rw [Finset.sum_cons]
    exact le_trans (le_min h1 h2) (padicValRat.min_le_padicValRat_add hne)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hdvd : p ^ (t + 1) ∣ y` using `(pow_dvd_pow p (Nat.succ_le_of_lt h)).trans pow_padicValNat_dvd`. Conclude with `absurd (Nat.le_of_dvd (by omega) hdvd) (not_le.2 hyP)`.
-/
theorem padicValNat_le_of_lt_pow {p t y : ℕ} [hp : Fact p.Prime] (hy : 1 ≤ y)
    (hyP : y < p ^ (t + 1)) : padicValNat p y ≤ t := by
  by_contra h
  push_neg at h
  have hdvd : p ^ (t + 1) ∣ y :=
    (pow_dvd_pow p (Nat.succ_le_of_lt h)).trans pow_padicValNat_dvd
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (not_le.2 hyP)

/- English proof (translation)
Introduce `p t s hp`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hPpos : (0 : ℚ) < ((p ^ (t + 1) : ℕ) : ℚ)`. Establish `: 0 < p ^ (t + 1)` using `pow_pos hp.pos _`. Conclude with `this` after adjusting the coercions.

Establish `hP0 : ((p ^ (t + 1) : ℕ) : ℚ) ≠ 0` using `hPpos.ne'`. Rewrite using `[Finset.mul_sum]`. Use `le_padicValRat_sum_of_pos (p := p) (s : ℤ) (F := fun y => ((p ^ (t + 1) : ℕ) : ℚ) ^ s * (1 / (y : ℚ) ^ s)) (S := Ico 1 (p ^ (t + 1))) ?_ ?_ ?_` and prove the remaining obligations. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_Ico]`.

Conclude with `⟨le_rfl, Nat.one_lt_pow (Nat.succ_ne_zero t) hp.one_lt⟩`. Introduce `y hy`. Rewrite `hy` using `[Finset.mem_Ico]`. Establish `hy0 : (0 : ℚ) < (y : ℚ)` using `by exact_mod_cast (show 0 < y by omega)`. Conclude with `mul_pos (pow_pos hPpos _) (one_div_pos.2 (pow_pos hy0 _))`.

Introduce `y hy`. Rewrite `hy` using `[Finset.mem_Ico]`. Establish `hy0 : (y : ℚ) ≠ 0` using `by exact_mod_cast (show y ≠ 0 by omega)`. Establish `hvy : padicValNat p y ≤ t` using `padicValNat_le_of_lt_pow hy.1 hy.2`. Rewrite using `[padicValRat.mul (pow_ne_zero _ hP0) (one_div_ne_zero (pow_ne_zero _ hy0)), padicValRat.pow _, one_div, padicValRat.inv, padicValRat.pow _, padicValRat.of_nat, padicValRat.of_nat, padicValNat.prime_pow]`.

Establish `hm : (s : ℤ) * (padicValNat p y : ℤ) ≤ (s : ℤ) * (t : ℤ)` using `mul_le_mul_of_nonneg_left (by exact_mod_cast hvy) (by positivity)`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem padicValHarmonicPowerSum : HarmonicVal := by
  intro p t s hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hPpos : (0 : ℚ) < ((p ^ (t + 1) : ℕ) : ℚ) := by
    have : 0 < p ^ (t + 1) := pow_pos hp.pos _
    exact_mod_cast this
  have hP0 : ((p ^ (t + 1) : ℕ) : ℚ) ≠ 0 := hPpos.ne'
  rw [Finset.mul_sum]
  refine le_padicValRat_sum_of_pos (p := p) (s : ℤ)
    (F := fun y => ((p ^ (t + 1) : ℕ) : ℚ) ^ s * (1 / (y : ℚ) ^ s))
    (S := Ico 1 (p ^ (t + 1))) ?_ ?_ ?_
  · refine ⟨1, ?_⟩
    rw [Finset.mem_Ico]
    exact ⟨le_rfl, Nat.one_lt_pow (Nat.succ_ne_zero t) hp.one_lt⟩
  · intro y hy
    rw [Finset.mem_Ico] at hy
    have hy0 : (0 : ℚ) < (y : ℚ) := by exact_mod_cast (show 0 < y by omega)
    exact mul_pos (pow_pos hPpos _) (one_div_pos.2 (pow_pos hy0 _))
  · intro y hy
    rw [Finset.mem_Ico] at hy
    have hy0 : (y : ℚ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
    have hvy : padicValNat p y ≤ t := padicValNat_le_of_lt_pow hy.1 hy.2
    rw [padicValRat.mul (pow_ne_zero _ hP0) (one_div_ne_zero (pow_ne_zero _ hy0)),
      padicValRat.pow _, one_div, padicValRat.inv, padicValRat.pow _,
      padicValRat.of_nat, padicValRat.of_nat, padicValNat.prime_pow]
    have hm : (s : ℤ) * (padicValNat p y : ℤ) ≤ (s : ℤ) * (t : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hvy) (by positivity)
    push_cast
    nlinarith

/- English proof (translation)
Introduce `s`. Establish `hcoeff : (Polynomial.bernoulli (s + 1)).coeff (s + 1) = 1`. Rewrite using `[Polynomial.bernoulli_def, Polynomial.finset_sum_coeff, Finset.sum_eq_single (s + 1)]`. Simplify using `[Polynomial.coeff_monomial]`. Introduce `b _ hb`.

Rewrite using `[Polynomial.coeff_monomial, if_neg hb]`. Introduce `h`. Conclude with `absurd (Finset.self_mem_range_succ (s + 1)) h`. Establish `hle : (Polynomial.bernoulli (s + 1)).natDegree ≤ s + 1`. Rewrite using `[Polynomial.bernoulli_def]`.

Apply `Polynomial.natDegree_sum_le_of_forall_le` to reduce the goal to its premises. Introduce `i hi`. Conclude with `(Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))`. Establish `hdeg : (Polynomial.bernoulli (s + 1)).natDegree = s + 1` using `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; exact one_ne_zero)`. Establish `hs : ((s : ℚ) + 1) ≠ 0` using `by positivity`.

Use `⟨Polynomial.C (1 / ((s : ℚ) + 1)) * (Polynomial.bernoulli (s + 1) - Polynomial.C (bernoulli (s + 1))), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.natDegree_C_mul (one_div_ne_zero hs), Polynomial.natDegree_sub_C, hdeg]`. Introduce `n`. Establish `h` using `Polynomial.sum_range_pow_eq_bernoulli_sub n s`. Simplify using `only [Nat.succ_eq_add_one] at h`.

Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]`. Rewrite using `[← h, ← mul_assoc, one_div_mul_cancel hs, one_mul]`.
-/
theorem powerSumPolynomial : PowerSumPoly := by
  intro s
  classical
  have hcoeff : (Polynomial.bernoulli (s + 1)).coeff (s + 1) = 1 := by
    rw [Polynomial.bernoulli_def, Polynomial.finset_sum_coeff,
      Finset.sum_eq_single (s + 1)]
    · simp [Polynomial.coeff_monomial]
    · intro b _ hb
      rw [Polynomial.coeff_monomial, if_neg hb]
    · intro h
      exact absurd (Finset.self_mem_range_succ (s + 1)) h
  have hle : (Polynomial.bernoulli (s + 1)).natDegree ≤ s + 1 := by
    rw [Polynomial.bernoulli_def]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have hdeg : (Polynomial.bernoulli (s + 1)).natDegree = s + 1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; exact one_ne_zero)
  have hs : ((s : ℚ) + 1) ≠ 0 := by positivity
  refine ⟨Polynomial.C (1 / ((s : ℚ) + 1)) *
    (Polynomial.bernoulli (s + 1) - Polynomial.C (bernoulli (s + 1))), ?_, ?_⟩
  · rw [Polynomial.natDegree_C_mul (one_div_ne_zero hs), Polynomial.natDegree_sub_C, hdeg]
  · intro n
    have h := Polynomial.sum_range_pow_eq_bernoulli_sub n s
    simp only [Nat.succ_eq_add_one] at h
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
    rw [← h, ← mul_assoc, one_div_mul_cancel hs, one_mul]

end Formalism.GrowthSums
