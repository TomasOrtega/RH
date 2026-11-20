import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

set_option autoImplicit false

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `a i hia`. Simplify using `only [symMat, Matrix.of_apply]`. Use `Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ hia)` and prove the remaining obligations. Rewrite using `[← C_pow]`. Use `(natDegree_mul_C_le _ _).trans ?_` and prove the remaining obligations.

Establish `h1 : (C (A 0 1) + C (A 1 1) * X).natDegree ≤ 1` using `by compute_degree`. Simplify using `using natDegree_pow_le_of_le (i : ℕ) h1`.
-/
theorem symMat_upperTriangular {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    (symMat m A).BlockTriangular id := by
  intro a i hia
  simp only [symMat, Matrix.of_apply]
  refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ hia)
  rw [← C_pow]
  refine (natDegree_mul_C_le _ _).trans ?_
  have h1 : (C (A 0 1) + C (A 1 1) * X).natDegree ≤ 1 := by compute_degree
  simpa using natDegree_pow_le_of_le (i : ℕ) h1

/- English proof (translation)
Simplify using `only [symMat, Matrix.of_apply]`. Rewrite using `[← C_pow, coeff_mul_C]`. Use `congr 1`. Establish `h1 : (C (A 0 1) + C (A 1 1) * X).natDegree ≤ 1` using `by compute_degree`. Use `coeff_pow_of_natDegree_le (m := (i : ℕ)) h1` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem symMat_diag {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (i : Fin (m + 1)) :
    symMat m A i i = A 1 1 ^ (i : ℕ) * A 0 0 ^ (m - i) := by
  simp only [symMat, Matrix.of_apply]
  rw [← C_pow, coeff_mul_C]
  congr 1
  have h1 : (C (A 0 1) + C (A 1 1) * X).natDegree ≤ 1 := by compute_degree
  have := coeff_pow_of_natDegree_le (m := (i : ℕ)) h1
  rw [mul_one] at this
  rw [this]
  simp

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (symMat_upperTriangular m A)]`. Simplify using `only [symMat_diag]`. Rewrite using `[Matrix.det_fin_two, h, mul_zero, sub_zero]`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => A 1 1 ^ i * A 0 0 ^ (m - i)) (m + 1), Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, mul_pow, mul_comm]`. Establish `hs : ∑ i ∈ Finset.range (m + 1), i = m * (m + 1) / 2`.

Rewrite using `[Finset.sum_range_id]`. Simplify using `[mul_comm]`. Establish `hr : ∑ i ∈ Finset.range (m + 1), (m - i) = m * (m + 1) / 2`. Rewrite using `[← hs]`. Conclude with `Finset.sum_range_reflect (fun i => i) (m + 1)`.

Rewrite using `[hs, hr]`.
-/
theorem det_symMat_of_upper {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (h : A 1 0 = 0) :
    (symMat m A).det = A.det ^ (m * (m + 1) / 2) := by
  rw [Matrix.det_of_upperTriangular (symMat_upperTriangular m A)]
  simp only [symMat_diag]
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero]
  rw [Fin.prod_univ_eq_prod_range (fun i => A 1 1 ^ i * A 0 0 ^ (m - i)) (m + 1), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, mul_pow, mul_comm]
  have hs : ∑ i ∈ Finset.range (m + 1), i = m * (m + 1) / 2 := by
    rw [Finset.sum_range_id]; simp [mul_comm]
  have hr : ∑ i ∈ Finset.range (m + 1), (m - i) = m * (m + 1) / 2 := by
    rw [← hs]
    exact Finset.sum_range_reflect (fun i => i) (m + 1)
  rw [hs, hr]

/- English proof (translation)
Simplify using `only [ord, map_pow, WithZero.log_pow, nsmul_eq_mul, mul_neg]`.
-/
theorem ord_pow' {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (x : F) (N : ℕ) :
    ord v (x ^ N) = (N : ℤ) * ord v x := by
  simp only [ord, map_pow, WithZero.log_pow, nsmul_eq_mul, mul_neg]

/- English proof (translation)
Use `⟨fun a i => ?_, ?_⟩` and prove the remaining obligations. Set `A' : Matrix (Fin 2) (Fin 2) v.O` to `fun i j => ⟨A i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu.1 i j)⟩`. Establish `e : A'.map v.O.subtype = A` using `by ext i j; rfl`. Rewrite using `[← e, ← symMat_map]`. Conclude with `(Valuation.mem_valuationSubring_iff _ _).1 (symMat m A' a i).2`.

Rewrite using `[det_symMat_of_upper m A hA, map_pow, hu.2, one_pow]`.
-/
theorem unimod_symMat {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) F) (hA : A 1 0 = 0) (hu : Unimod v A) : Unimod v (symMat m A) := by
  refine ⟨fun a i => ?_, ?_⟩
  · let A' : Matrix (Fin 2) (Fin 2) v.O := fun i j => ⟨A i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu.1 i j)⟩
    have e : A'.map v.O.subtype = A := by ext i j; rfl
    rw [← e, ← symMat_map]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (symMat m A' a i).2
  · rw [det_symMat_of_upper m A hA, map_pow, hu.2, one_pow]

/- English proof (translation)
Introduce `k F _ _ _ _ m g hg h0`. Use `⟨⟨fun v => ?_, hg.2.subset fun v hv hu => hv (unimod_symMat v m (g v) (h0 v) hu)⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[det_symMat_of_upper m (g v) (h0 v)]`. Conclude with `pow_ne_zero _ (hg.1 v)`. Simplify using `only [deg, det_symMat_of_upper m _ (h0 _), ord_pow']`.

Rewrite using `[mul_finsum]`.
-/
theorem admissible_degree_symmetricPowerFamily : ∀ (k F : Type) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (m : ℕ)
    (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) →
      admitted (fun v => symMat m (g v)) ∧ deg (fun v => symMat m (g v)) = ((m * (m + 1) / 2 : ℕ) : ℤ) * deg g := by
  intro k F _ _ _ _ m g hg h0
  refine ⟨⟨fun v => ?_, hg.2.subset fun v hv hu => hv (unimod_symMat v m (g v) (h0 v) hu)⟩, ?_⟩
  · rw [det_symMat_of_upper m (g v) (h0 v)]
    exact pow_ne_zero _ (hg.1 v)
  · simp only [deg, det_symMat_of_upper m _ (h0 _), ord_pow']
    rw [mul_finsum]

end GlobalTheory.Nef
