import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open Real

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Break down `lt_or_ge N p with h | h` into its components or cases. Rewrite using `[Nat.div_eq_of_lt h]`. Conclude with `Nat.zero_le _`. Rewrite using `[padicValNat_factorial (b := Nat.log p N + 1) (Nat.lt_succ_self _)]`.

Establish `h1 : 1 ∈ Finset.Ico 1 (Nat.log p N + 1)`. Use `Nat.log_pos hp.one_lt h` as an intermediate fact. Simplify using `only [Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Use `Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1` as an intermediate fact.

Simplify using `using this`.
-/
lemma div_le_padicValNat_factorial (N p : ℕ) (hp : p.Prime) :
    N / p ≤ padicValNat p N.factorial := by
  have := Fact.mk hp
  rcases lt_or_ge N p with h | h
  · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
  · rw [padicValNat_factorial (b := Nat.log p N + 1) (Nat.lt_succ_self _)]
    have h1 : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := by
      have := Nat.log_pos hp.one_lt h
      simp only [Finset.mem_Ico]; omega
    have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this

/- English proof (translation)
Establish `: ((∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p) : ℕ) : ℤ) ∣ (N.factorial : ℤ)`. Use `push_cast`. Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises. Introduce `p hp q hq hpq`. Establish `hp'` using `(Finset.mem_filter.1 hp).2`.

Establish `hq'` using `(Finset.mem_filter.1 hq).2`. Simplify using `only [Function.onFun]`. Conclude with `Nat.isCoprime_iff_coprime.2 (Nat.coprime_pow_primes _ _ hp' hq' hpq)` after adjusting the coercions. Introduce `p hp`. Establish `hp'` using `(Finset.mem_filter.1 hp).2`.

Conclude with `(pow_dvd_pow p (div_le_padicValNat_factorial N p hp')).trans pow_padicValNat_dvd` after adjusting the coercions. Conclude with `this` after adjusting the coercions.
-/
lemma prod_pow_div_dvd_factorial (N : ℕ) :
    (∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p)) ∣ N.factorial := by
  have : ((∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p) : ℕ) : ℤ) ∣ (N.factorial : ℤ) := by
    push_cast
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      simp only [Function.onFun]
      exact_mod_cast Nat.isCoprime_iff_coprime.2 (Nat.coprime_pow_primes _ _ hp' hq' hpq)
    · intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      exact_mod_cast (pow_dvd_pow p (div_le_padicValNat_factorial N p hp')).trans
        pow_padicValNat_dvd
  exact_mod_cast this

/- English proof (translation)
Use `⟨Real.log 4, fun B hB => ?_⟩` and prove the remaining obligations. Use `set N := ⌊B⌋₊ with hN`. Use `set P := (Finset.Iic N).filter Nat.Prime with hP`. Establish `hN2 : 2 ≤ N` using `Nat.le_floor (by exact_mod_cast hB)`. Establish `hNpos : (0 : ℝ) < N` using `by exact_mod_cast (by omega : 0 < N)`.

Establish `hNB : (N : ℝ) ≤ B` using `Nat.floor_le (by linarith)`. Establish `hpos : ∀ p ∈ P, (1 : ℝ) ≤ p` using `fun p hp => by`. Conclude with `(Finset.mem_filter.1 hp).2.one_lt.le` after adjusting the coercions. Establish `hle : ∏ p ∈ P, p ^ (N / p) ≤ N ^ N` using `(Nat.le_of_dvd (Nat.factorial_pos _) (prod_pow_div_dvd_factorial N)).trans (Nat.factorial_le_pow N)`. Establish `hlog : ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p ≤ N * Real.log N`.

Establish `hprod : (0 : ℝ) < ∏ p ∈ P, ((p : ℝ) ^ (N / p))` using `Finset.prod_pos fun p hp => pow_pos (by linarith [hpos p hp]) _`. Establish `h` using `Real.log_le_log hprod (show ∏ p ∈ P, ((p : ℝ) ^ (N / p)) ≤ (N : ℝ) ^ N by exact_mod_cast hle)`. Rewrite `h` using `[Real.log_prod (fun p hp => (pow_pos (by linarith [hpos p hp]) _).ne'), Real.log_pow]`. Simplify `h` using `[Real.log_pow]`. Establish `hfloor : ∀ p ∈ P, ((N : ℝ) / p - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p` using `fun p hp => mul_le_mul_of_nonneg_right (by rw [← Nat.floor_div_eq_div (K := ℝ)]; exact (Nat.sub_one_lt_floor _).le) (Real.log_nonneg (hpos p hp))`.

Establish `htheta : ∑ p ∈ P, Real.log p ≤ Real.log 4 * N`. Establish `h` using `Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hNpos.le`. Establish `hset : P = (Finset.Ioc 0 ⌊(N : ℝ)⌋₊).filter Nat.Prime`. Rewrite using `[Nat.floor_natCast, hP]`. Use extensionality with `p`.

Simplify using `only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨h2.pos, h1⟩, h2⟩`. Introduce and unpack `⟨⟨-, h1⟩, h2⟩`.

Conclude with `⟨h1, h2⟩`. Rewrite using `[hset]`. Conclude with `h`. Establish `key : (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p ≤ N * Real.log N`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p := Finset.sum_le_sum hfloor`. Use `_ ≤ N * Real.log N := hlog`.

Establish `hS : ∑ p ∈ P, Real.log p / p ≤ Real.log N + Real.log 4`. Establish `: (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4)`. Rewrite using `[mul_add]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_left this hNpos`.

Establish `hlogNB : Real.log N ≤ Real.log B` using `Real.log_le_log hNpos hNB`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem MertensUpper.proof : MertensUpper.Statement := by
  refine ⟨Real.log 4, fun B hB => ?_⟩
  set N := ⌊B⌋₊ with hN
  set P := (Finset.Iic N).filter Nat.Prime with hP
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hB)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNB : (N : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hpos : ∀ p ∈ P, (1 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le

  have hle : ∏ p ∈ P, p ^ (N / p) ≤ N ^ N :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (prod_pow_div_dvd_factorial N)).trans
      (Nat.factorial_le_pow N)
  have hlog : ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p ≤ N * Real.log N := by
    have hprod : (0 : ℝ) < ∏ p ∈ P, ((p : ℝ) ^ (N / p)) :=
      Finset.prod_pos fun p hp => pow_pos (by linarith [hpos p hp]) _
    have h := Real.log_le_log hprod
      (show ∏ p ∈ P, ((p : ℝ) ^ (N / p)) ≤ (N : ℝ) ^ N by exact_mod_cast hle)
    rw [Real.log_prod (fun p hp => (pow_pos (by linarith [hpos p hp]) _).ne'),
      Real.log_pow] at h
    simpa [Real.log_pow] using h

  have hfloor : ∀ p ∈ P, ((N : ℝ) / p - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p :=
    fun p hp => mul_le_mul_of_nonneg_right
      (by rw [← Nat.floor_div_eq_div (K := ℝ)]; exact (Nat.sub_one_lt_floor _).le)
      (Real.log_nonneg (hpos p hp))

  have htheta : ∑ p ∈ P, Real.log p ≤ Real.log 4 * N := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hNpos.le
    have hset : P = (Finset.Ioc 0 ⌊(N : ℝ)⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast, hP]
      ext p
      simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, h1⟩, h2⟩
      · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    rw [hset]; exact h
  have key : (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p ≤ N * Real.log N := by
    calc (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p
        = ∑ p ∈ P, ((N : ℝ) / p - 1) * Real.log p := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ ≤ ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p := Finset.sum_le_sum hfloor
      _ ≤ N * Real.log N := hlog
  have hS : ∑ p ∈ P, Real.log p / p ≤ Real.log N + Real.log 4 := by
    have : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
      rw [mul_add]; linarith
    exact le_of_mul_le_mul_left this hNpos
  have hlogNB : Real.log N ≤ Real.log B := Real.log_le_log hNpos hNB
  linarith

end GroundTheory.Heights₂.Heights.Model
