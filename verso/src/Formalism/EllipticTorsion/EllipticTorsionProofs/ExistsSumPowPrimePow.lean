import Mathlib
import Formalism.EllipticTorsion.EllipticTorsionWeights

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

namespace FrobeniusExpansion

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `[zero_pow (pow_ne_zero n hp.ne_zero)]`. Consider the case `insert a s ha ih`.

Take `⟨r, hr⟩` from `ih`. Take `⟨r', hr'⟩` from `exists_add_pow_prime_pow_eq hp (f a) (∑ i ∈ s, f i) n`. Use `⟨f a * (∑ i ∈ s, f i) * r' + r, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_sum_pow_prime_pow {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → A) (n : ℕ) :
    ∃ r : A, (∑ i ∈ s, f i) ^ (p ^ n) = ∑ i ∈ s, f i ^ (p ^ n) + (p : A) * r := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp [zero_pow (pow_ne_zero n hp.ne_zero)]
  | insert a s ha ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hp (f a) (∑ i ∈ s, f i) n
    refine ⟨f a * (∑ i ∈ s, f i) * r' + r, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]
    ring

end FrobeniusExpansion

open MvPolynomial in
/- English proof (translation)
Introduce `K _ _ p hp _hp1 m j a b ha hab α`. Use `set R := unitBall K`. Set `a' : Fin m → R` to `fun e => ⟨a e, ha e⟩`. Take `⟨r, hr⟩` from `FrobeniusExpansion.exists_sum_pow_prime_pow (A := MvPolynomial (Fin m) R) hp Finset.univ (fun e => C (a' e) * X e) j`. Establish `hmap : (∑ e, C (a e) * X e : MvPolynomial (Fin m) K) = map R.subtype (∑ e, C (a' e) * X e)`.

Simplify using `[a']`. Establish `key : (∑ e, C (a e) * X e : MvPolynomial (Fin m) K) ^ (p ^ j) - ∑ e, C (b e) * X e ^ (p ^ j) = ∑ e, C (a e ^ (p ^ j) - b e) * X e ^ (p ^ j) + C (p : K) * map R.subtype r`. Rewrite using `[hmap, ← map_pow, hr, map_add, map_sum, map_mul, map_natCast]`. Simplify using `only [map_pow, map_mul, map_C, map_X, mul_pow, map_sub, sub_mul, Finset.sum_sub_distrib, map_natCast]`. Simplify using `[a']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, coeff_add, coeff_sum, coeff_C_mul, coeff_map]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun e _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_C_mul, coeff_X_pow, norm_mul]`.

Use `split_ifs`. Simplify using `using hab e`. Simplify using the standard rewrite rules. Rewrite using `[norm_mul]`. Establish `h1 : ‖((coeff α r : R) : K)‖ ≤ 1` using `(coeff α r).2`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem frobenius_expansion : FrobExpand := by
  intro K _ _ p hp _hp1 m j a b ha hab α
  classical
  set R := unitBall K
  let a' : Fin m → R := fun e => ⟨a e, ha e⟩
  obtain ⟨r, hr⟩ := FrobeniusExpansion.exists_sum_pow_prime_pow (A := MvPolynomial (Fin m) R) hp
    Finset.univ (fun e => C (a' e) * X e) j
  have hmap : (∑ e, C (a e) * X e : MvPolynomial (Fin m) K)
      = map R.subtype (∑ e, C (a' e) * X e) := by
    simp [a']
  have key : (∑ e, C (a e) * X e : MvPolynomial (Fin m) K) ^ (p ^ j)
        - ∑ e, C (b e) * X e ^ (p ^ j)
      = ∑ e, C (a e ^ (p ^ j) - b e) * X e ^ (p ^ j)
        + C (p : K) * map R.subtype r := by
    rw [hmap, ← map_pow, hr, map_add, map_sum, map_mul, map_natCast]
    simp only [map_pow, map_mul, map_C, map_X, mul_pow, map_sub, sub_mul,
      Finset.sum_sub_distrib, map_natCast]
    simp [a']
    ring
  rw [key, coeff_add, coeff_sum, coeff_C_mul, coeff_map]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun e _ => ?_
    rw [coeff_C_mul, coeff_X_pow, norm_mul]
    split_ifs
    · simpa using hab e
    · simp
  · rw [norm_mul]
    have h1 : ‖((coeff α r : R) : K)‖ ≤ 1 := (coeff α r).2
    calc ‖(p : K)‖ * ‖((coeff α r : R) : K)‖ ≤ ‖(p : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖(p : K)‖ := mul_one _

end Formalism.ELL
