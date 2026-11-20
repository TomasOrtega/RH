import Mathlib

namespace GlobalTheory.LaurentFrac

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ha i)]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem prod_zpow_mul {K : Type} [Field K] {I : Type} [Fintype I] (a : I → K) (N : I → ℤ)
    (ha : ∀ i, a i ≠ 0) :
    (∏ i, a i ^ N i) * ∏ i, a i ^ (-N i).toNat = ∏ i, a i ^ (N i).toNat := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ha i)]
  congr 1
  omega

/- English proof (translation)
Use `⟨∏ i, s i ^ (N i).toNat, ∏ i, s i ^ (-N i).toNat, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ (hs i)`.

Simplify using `only [map_prod, map_pow]`. Use `prod_zpow_mul _ N fun i => ?_` and prove the remaining obligations. Establish `h : s i ≠ 0` using `fun h => hs i (by rw [h, map_zero])`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h`. Simplify using `only [map_prod, map_pow]`.

Use `prod_zpow_mul _ N fun i => ?_` and prove the remaining obligations. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs i)`.
-/
theorem exists_frac (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (N : I → ℤ) (hs : ∀ i, θ (s i) ≠ 0) :
    ∃ x y : R, θ y ≠ 0 ∧
      (∏ i, algebraMap R (FractionRing R) (s i) ^ N i) * algebraMap R _ y = algebraMap R _ x ∧
      (∏ i, algebraMap V (FractionRing V) (θ (s i)) ^ N i) * algebraMap V _ (θ y)
        = algebraMap V _ (θ x) := by
  refine ⟨∏ i, s i ^ (N i).toNat, ∏ i, s i ^ (-N i).toNat, ?_, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [map_pow]
    exact pow_ne_zero _ (hs i)
  · simp only [map_prod, map_pow]
    refine prod_zpow_mul _ N fun i => ?_
    have h : s i ≠ 0 := fun h => hs i (by rw [h, map_zero])
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h
  · simp only [map_prod, map_pow]
    refine prod_zpow_mul _ N fun i => ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs i)

end GlobalTheory.LaurentFrac
