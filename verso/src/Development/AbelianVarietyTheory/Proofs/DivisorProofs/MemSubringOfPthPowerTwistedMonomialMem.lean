import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ p A n x I J t r g hp hA hr h`. Establish `hP0 : (∏ j ∈ I \ J, (x j : K)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)`. Establish `hQ0 : (∏ j ∈ J, (x j : K)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)`. Establish `hcast : ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) = (t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j)` using `by push_cast; rfl`. Rewrite `h` using `[hcast]`.

Establish `hpow : ∀ j ∈ J, (x j : K) ^ p = (x j : K) ^ (r j) * (x j : K) * (x j : K) ^ (p - 1 - r j)`. Introduce `j _`. Rewrite using `[← pow_succ, ← pow_add]`. Use `congr 1`. Use `hr j` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hprod : (∏ j ∈ J, (x j : K)) ^ p = (∏ j ∈ J, (x j : K) ^ (r j)) * (∏ j ∈ J, (x j : K)) * ∏ j ∈ J, (x j : K) ^ (p - 1 - r j)`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl hpow`. Establish `hS : ∏ j ∈ J ∪ I \ J, (x j : K) = (∏ j ∈ J, (x j : K)) * ∏ j ∈ I \ J, (x j : K)` using `Finset.prod_union Finset.disjoint_sdiff`.

Establish `hB : ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) ∈ A` using `Subring.prod_mem _ (fun j _ => Subring.pow_mem _ (hA.mem j) _)`. Establish `key : (g * t * ∏ j ∈ J, (x j : K)) ^ p / ∏ j ∈ J ∪ I \ J, (x j : K) = (g ^ p * ((t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j)) / ∏ j ∈ I \ J, (x j : K)) * ∏ j ∈ J, (x j : K) ^ (p - 1 - r j)`. Rewrite using `[hS, mul_pow, mul_pow, hprod]`. Clear the denominators using the available nonvanishing facts. Establish `h2` using `hA.root (J ∪ I \ J) _ p hp (key ▸ A.mul_mem h hB)`.

Establish `e : (g * t * ∏ j ∈ J, (x j : K)) / ∏ j ∈ J ∪ I \ J, (x j : K) = g * t / ∏ j ∈ I \ J, (x j : K)`. Rewrite using `[hS]`. Clear the denominators using the available nonvanishing facts. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
theorem LogDR.round_coeff_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  intro K _ p A n x I J t r g hp hA hr h
  have hP0 : (∏ j ∈ I \ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hQ0 : (∏ j ∈ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hcast : ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) = (t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j) := by
    push_cast; rfl
  rw [hcast] at h
  have hpow : ∀ j ∈ J, (x j : K) ^ p = (x j : K) ^ (r j) * (x j : K) * (x j : K) ^ (p - 1 - r j) := by
    intro j _
    rw [← pow_succ, ← pow_add]
    congr 1
    have := hr j
    omega
  have hprod : (∏ j ∈ J, (x j : K)) ^ p = (∏ j ∈ J, (x j : K) ^ (r j)) * (∏ j ∈ J, (x j : K)) *
      ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hpow
  have hS : ∏ j ∈ J ∪ I \ J, (x j : K) = (∏ j ∈ J, (x j : K)) * ∏ j ∈ I \ J, (x j : K) :=
    Finset.prod_union Finset.disjoint_sdiff
  have hB : ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) ∈ A :=
    Subring.prod_mem _ (fun j _ => Subring.pow_mem _ (hA.mem j) _)
  have key : (g * t * ∏ j ∈ J, (x j : K)) ^ p / ∏ j ∈ J ∪ I \ J, (x j : K) =
      (g ^ p * ((t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j)) / ∏ j ∈ I \ J, (x j : K)) *
        ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [hS, mul_pow, mul_pow, hprod]
    field_simp
  have h2 := hA.root (J ∪ I \ J) _ p hp (key ▸ A.mul_mem h hB)
  have e : (g * t * ∏ j ∈ J, (x j : K)) / ∏ j ∈ J ∪ I \ J, (x j : K) = g * t / ∏ j ∈ I \ J, (x j : K) := by
    rw [hS]
    field_simp
  rwa [e] at h2

end GlobalTheory
