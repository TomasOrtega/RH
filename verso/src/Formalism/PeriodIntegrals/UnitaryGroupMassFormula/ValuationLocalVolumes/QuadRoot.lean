import Mathlib

noncomputable section

open Polynomial IsLocalRing

namespace PI.OmVf

/- English proof (translation)
Take `⟨u, hu⟩` from `hB.exists_right_inv`. Establish `haK : A * u * u * K ∈ maximalIdeal R`. Establish `h1 : A * u * u * K = A * (u * u * K)` using `by ring`. Rewrite using `[h1]`. Conclude with `Ideal.mul_mem_right _ _ hA`.

Take `⟨w, hwr, hwm⟩` from `HenselianLocalRing.is_henselian (X ^ 2 + X + Polynomial.C (A * u * u * K)) (by monicity!) 0 (by simpa using haK) (by simp)`. Establish `hw : w ^ 2 + w + A * u * u * K = 0` using `by simpa using hwr`. Establish `hwm' : w ∈ maximalIdeal R` using `by simpa using hwm`. Establish `hunit : IsUnit (1 + w)`. Assume the negation of the conclusion as `hn`.

Establish `h1 : 1 + w ∈ maximalIdeal R` using `(mem_maximalIdeal _).mpr hn`. Establish `h2 : (1 : R) ∈ maximalIdeal R`. Establish `e : (1 : R) = (1 + w) - w` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ h1 hwm'`.

Conclude with `(maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)`. Take `⟨v, hv⟩` from `hunit.exists_right_inv`. Use `⟨-(u * K * v), ?_⟩` and prove the remaining obligations. Take the linear combination `K * v ^ 2 * hw - K * (2 - v + ((1 + w) * v - 1)) * hv - K * v * hu`.
-/
theorem quad_root {R : Type*} [CommRing R] [HenselianLocalRing R] (A B K : R) (hA : A ∈ maximalIdeal R)
    (hB : IsUnit B) : ∃ s : R, A * s ^ 2 + B * s + K = 0 := by
  obtain ⟨u, hu⟩ := hB.exists_right_inv
  have haK : A * u * u * K ∈ maximalIdeal R := by
    have h1 : A * u * u * K = A * (u * u * K) := by ring
    rw [h1]; exact Ideal.mul_mem_right _ _ hA
  obtain ⟨w, hwr, hwm⟩ := HenselianLocalRing.is_henselian
    (X ^ 2 + X + Polynomial.C (A * u * u * K)) (by monicity!) 0
    (by simpa using haK) (by simp)
  have hw : w ^ 2 + w + A * u * u * K = 0 := by simpa using hwr
  have hwm' : w ∈ maximalIdeal R := by simpa using hwm
  have hunit : IsUnit (1 + w) := by
    by_contra hn
    have h1 : 1 + w ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hn
    have h2 : (1 : R) ∈ maximalIdeal R := by
      have e : (1 : R) = (1 + w) - w := by ring
      rw [e]; exact Ideal.sub_mem _ h1 hwm'
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  refine ⟨-(u * K * v), ?_⟩
  linear_combination K * v ^ 2 * hw - K * (2 - v + ((1 + w) * v - 1)) * hv - K * v * hu

end PI.OmVf
