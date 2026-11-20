import Mathlib

/- English proof (translation)
Introduce `S _ J p _ hp x hx j`. Proceed by induction on `j with`. Consider the case `zero => simpa using hx`. Consider the case `succ j ih`. Establish `h1 : x ^ p ^ j - 1 ∈ J` using `Ideal.pow_le_self (Nat.succ_ne_zero j) ih`.

Establish `h2 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i) ∈ J`. Establish `h3 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i) = (∑ i ∈ Finset.range p, ((x ^ p ^ j) ^ i - 1)) + (p : S)`. Simplify using `[Finset.sum_sub_distrib]`. Rewrite using `[h3]`. Use `J.add_mem (J.sum_mem fun i _ => ?_) hp` and prove the remaining obligations.

Conclude with `J.mem_of_dvd (sub_one_dvd_pow_sub_one _ i) h1`. Rewrite using `[pow_succ p j, pow_mul, ← mul_geom_sum, pow_succ J (j + 1)]`. Conclude with `Ideal.mul_mem_mul ih h2`.
-/
theorem UpperTheory.Reformulated.B.Qf4.pow_sub_one_mem :
    ∀ {S : Type} [inst : CommRing S] (J : Ideal S) (p : ℕ),
    Nat.Prime p → (↑p : S) ∈ J → ∀ (x : S), x - (1 : S) ∈ J → ∀ (j : ℕ), x ^ p ^ j - (1 : S) ∈ J ^ (j + (1 : ℕ)) := by
  intro S _ J p _ hp x hx j
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have h1 : x ^ p ^ j - 1 ∈ J := Ideal.pow_le_self (Nat.succ_ne_zero j) ih
    have h2 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i) ∈ J := by
      have h3 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i)
          = (∑ i ∈ Finset.range p, ((x ^ p ^ j) ^ i - 1)) + (p : S) := by
        simp [Finset.sum_sub_distrib]
      rw [h3]
      refine J.add_mem (J.sum_mem fun i _ => ?_) hp
      exact J.mem_of_dvd (sub_one_dvd_pow_sub_one _ i) h1
    rw [pow_succ p j, pow_mul, ← mul_geom_sum, pow_succ J (j + 1)]
    exact Ideal.mul_mem_mul ih h2
