import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

/- English proof (translation)
Establish `key : ∀ a : ℕ, x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a)) = ∑ t ∈ powersetCard a (univ : Finset (Fin n)), ∏ j ∈ t, (-(x * g j))`. Introduce `a`. Simplify using `only [esymm, map_sum, map_prod, aeval_X, mul_sum]`. Use `sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Rewrite using `[prod_neg, prod_mul_distrib, prod_const, (mem_powersetCard.1 ht).2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Fin.sum_univ_eq_sum_range (fun a => x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a))) (n + 1)]`. Simplify using `only [key]`. Establish `hc : n + 1 = #(univ : Finset (Fin n)) + 1` using `by simp`. Rewrite using `[hc, ← sum_powerset, ← prod_one_add]`.

Unfold `detOne`. Simplify using `only [sub_eq_add_neg]`.
-/
private lemma one_factor {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (n : ℕ) (x : R)
    (g : Fin n → R) :
    detOne x g = ∑ a : Fin (n + 1), x ^ (a : ℕ) * ((-1) ^ (a : ℕ) * aeval g (esymm (Fin n) K a)) := by
  have key : ∀ a : ℕ, x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a)) =
      ∑ t ∈ powersetCard a (univ : Finset (Fin n)), ∏ j ∈ t, (-(x * g j)) := by
    intro a
    simp only [esymm, map_sum, map_prod, aeval_X, mul_sum]
    refine sum_congr rfl fun t ht => ?_
    rw [prod_neg, prod_mul_distrib, prod_const, (mem_powersetCard.1 ht).2]
    ring
  rw [Fin.sum_univ_eq_sum_range (fun a => x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a))) (n + 1)]
  simp only [key]
  have hc : n + 1 = #(univ : Finset (Fin n)) + 1 := by simp
  rw [hc, ← sum_powerset, ← prod_one_add]
  unfold detOne
  simp only [sub_eq_add_neg]

/- English proof (translation)
Introduce `K R π _ _ _ _ _ n x g`. Simplify using `only [one_factor (K := K)]`. Rewrite using `[Fintype.prod_sum]`. Use `sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[prod_mul_distrib]`.
-/
theorem UpperTheory.Gal.Schur.expand :
    Expand := by
  intro K R π _ _ _ _ _ n x g
  simp only [one_factor (K := K)]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [prod_mul_distrib]
