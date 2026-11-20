import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `hS K ι _ _ _ n P hP`. Use `choose k0 hk0 using fun t => hS K n (P t) (hP t)`. Use `⟨univ.sup k0, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hle : ∀ t, k0 t ≤ k` using `fun t => (le_sup (mem_univ t)).trans hk`. Use `choose w hw using fun t => hk0 t k (hle t)`.

Use `⟨fun m => ∏ t, (w t (fun s => m (t, s)) * ∏ s, (-1 : K) ^ ((m (t, s) : Fin (n + 1)) : ℕ)), ?_⟩` and prove the remaining obligations. Introduce `R _ _ g`. Establish `step : ∀ t, aeval (g t) (P t) = ∑ m : Fin k → Fin (n + 1), (w t m * ∏ s, (-1 : K) ^ (m s : ℕ)) • ∏ s, ((-1) ^ (m s : ℕ) * aeval (g t) (esymm (Fin n) K (m s)))`. Introduce `t`. Use `conv_lhs => rw [hw t]`.

Simplify using `only [map_sum, map_smul, map_prod]`. Use `sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[prod_mul_distrib, Algebra.smul_def, Algebra.smul_def, map_mul, map_prod]`. Simplify using `only [map_pow, map_neg, map_one]`. Establish `hc : (∏ s, (-1 : R) ^ (m s : ℕ)) * ∏ s, (-1 : R) ^ (m s : ℕ) = 1`.

Rewrite using `[← prod_mul_distrib]`. Simplify using `[← mul_pow]`. Take the linear combination `(-(algebraMap K R (w t m) * ∏ s, aeval (g t) (esymm (Fin n) K (m s)))) * hc`. Simplify using `only [step]`. Rewrite using `[Fintype.prod_sum]`.

Use `Fintype.sum_equiv (Equiv.curry ι (Fin k) (Fin (n + 1))).symm _ _ fun M => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Simplify using `only [Equiv.curry_symm_apply, Function.uncurry_apply_pair, Algebra.smul_def, map_prod, prod_mul_distrib]`. Rewrite using `[← map_prod, prod_mul_distrib]`.
-/
theorem UpperTheory.Gal.Schur.spanProd_of :
    SpanE → SpanProd := by
  intro hS K ι _ _ _ n P hP
  choose k0 hk0 using fun t => hS K n (P t) (hP t)
  refine ⟨univ.sup k0, fun k hk => ?_⟩
  have hle : ∀ t, k0 t ≤ k := fun t => (le_sup (mem_univ t)).trans hk
  choose w hw using fun t => hk0 t k (hle t)
  refine ⟨fun m => ∏ t, (w t (fun s => m (t, s)) * ∏ s, (-1 : K) ^ ((m (t, s) : Fin (n + 1)) : ℕ)), ?_⟩
  intro R _ _ g
  have step : ∀ t, aeval (g t) (P t) = ∑ m : Fin k → Fin (n + 1),
      (w t m * ∏ s, (-1 : K) ^ (m s : ℕ)) • ∏ s, ((-1) ^ (m s : ℕ) * aeval (g t) (esymm (Fin n) K (m s))) := by
    intro t
    conv_lhs => rw [hw t]
    simp only [map_sum, map_smul, map_prod]
    refine sum_congr rfl fun m _ => ?_
    rw [prod_mul_distrib, Algebra.smul_def, Algebra.smul_def, map_mul, map_prod]
    simp only [map_pow, map_neg, map_one]
    have hc : (∏ s, (-1 : R) ^ (m s : ℕ)) * ∏ s, (-1 : R) ^ (m s : ℕ) = 1 := by
      rw [← prod_mul_distrib]
      simp [← mul_pow]
    linear_combination (-(algebraMap K R (w t m) * ∏ s, aeval (g t) (esymm (Fin n) K (m s)))) * hc
  simp only [step]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.curry ι (Fin k) (Fin (n + 1))).symm _ _ fun M => ?_
  rw [Fintype.prod_prod_type]
  simp only [Equiv.curry_symm_apply, Function.uncurry_apply_pair, Algebra.smul_def, map_prod,
    prod_mul_distrib]
  rw [← map_prod, prod_mul_distrib]
