import Mathlib
open scoped TensorProduct Classical
open Polynomial

namespace GlobalTheory.DescCoeff

/- English proof (translation)
Use `set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx`. Establish `hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ))`. Establish `h` using `Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`.

Simplify using `[hx, Algebra.TensorProduct.tmul_pow]`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hsum` using `aeval_eq_sum_range' hlt x`. Rewrite `hsum` using `[minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)]`.

Establish `hc` using `Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm`. Apply `minpoly.ne_zero hK` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[coeff_zero]`. Distinguish the cases in `hi : i < (minpoly F g).natDegree`.

Conclude with `hc ⟨i, hi⟩`. Conclude with `coeff_eq_zero_of_natDegree_lt (by omega)`.
-/
theorem natDegree_minpoly_le_one_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/- English proof (translation)
Use `set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz`. Establish `hzi : IsIntegral K z` using `IsIntegral.of_finite K z`. Establish `hyi : IsIntegral F y` using `IsIntegral.of_finite F y`. Establish `hzr : z = Algebra.TensorProduct.includeRight y` using `rfl`. Establish `hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K)`.

Apply `minpoly.dvd` to reduce the goal to its premises. Rewrite using `[aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hge` using `natDegree_minpoly_le_one_tmul K y hzi`. Use `eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd (by rw [natDegree_map]; exact hge)` as an intermediate fact. Rewrite using `[this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]`.
-/
theorem minpoly_one_tmul_eq {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (K : Type) [Field K] [Algebra F K] (y : B) :
    minpoly K ((1 : K) ⊗ₜ[F] y) = (minpoly F y).map (algebraMap F K) := by
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := natDegree_minpoly_le_one_tmul K y hzi
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
    (by rw [natDegree_map]; exact hge)
  rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]

end GlobalTheory.DescCoeff
