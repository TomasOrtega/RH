import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusCharacterOrthogonality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenFunctionCharacterSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMinpolyPowEqSumStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `F _ _ θ hθ m k l e hm`. Use `set q := Nat.card F with hq`. Establish `hq1 : 1 < q` using `Finite.one_lt_card`. Establish `hqm : 1 < q ^ m` using `Nat.one_lt_pow hm.ne' hq1`. Use `set N := q ^ m - 1 with hN`.

Establish `hN0 : 0 < N` using `by omega`. Establish `hcast : ((q : ℂ) ^ m - 1) = ((N : ℕ) : ℂ)`. Rewrite using `[hN, Nat.cast_sub hqm.le]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hNne : ((N : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast hN0.ne'`. Establish `htor` using `GlobalTheory.T.green_function_character_sum F θ m k (fun P => ∏ j, rootSum θ (e j) P) hm`. Establish `horth` using `(GlobalTheory.CuspGL.torus_orthogonality F θ hθ m hm).2`. Use `set T := {α : AlgebraicClosure F | α ^ N = 1} with hT`. Establish `hTfin : T.Finite`.

Apply `(Polynomial.nthRoots N (1 : AlgebraicClosure F)).toFinset.finite_toSet.subset` to reduce the goal to its premises. Introduce `α hα`. Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset]`. Conclude with `(Polynomial.mem_nthRoots hN0).2 hα`. Establish `key : ∀ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree))) = ∑ a : Fin l → Fin m, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ)))`.

Introduce `α hα`. Establish `hr : ∀ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a : Fin m, θ α ^ (e j * q ^ (a : ℕ))` using `fun j => (GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range F θ m (e j) α hm hα).trans (Finset.sum_range (fun a => θ α ^ (e j * q ^ a)))`. Repeatedly rewrite using `[hr]`. Rewrite using `[← Finset.mul_sum, ← star_sum, Finset.prod_univ_sum]`. Simplify using `only [Fintype.piFinset_univ, Finset.prod_pow_eq_pow_sum]`.

Establish `hsum : ∑ᶠ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree))) = ∑ a : Fin l → Fin m, ∑ᶠ α ∈ T, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ)))`. Rewrite using `[finsum_mem_congr rfl key, finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hTfin]`. Rewrite `htor` using `[hsum]`.

Rewrite `htor` using `[horth]`. Rewrite `htor` using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcast]`. Apply `mul_left_cancel₀ hNne` to reduce the goal to its premises. Rewrite using `[htor]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psiG_rootSum_pair_prod_rootSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (m k l : ℕ) (e : Fin l → ℕ), 0 < m → ∑ᶠ x, psiG (rootSum θ k) m x * star (chG (fun P => ∏ j, rootSum θ (e j) P) m x) = (Nat.card (GL (Fin m) F) : ℂ) * ((Finset.univ.filter fun a : Fin l → Fin m => k ≡ ∑ j, e j * Nat.card F ^ (a j : ℕ) [MOD Nat.card F ^ m - 1]).card : ℂ) := by
  intro F _ _ θ hθ m k l e hm
  set q := Nat.card F with hq
  have hq1 : 1 < q := Finite.one_lt_card
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq1
  set N := q ^ m - 1 with hN
  have hN0 : 0 < N := by omega
  have hcast : ((q : ℂ) ^ m - 1) = ((N : ℕ) : ℂ) := by
    rw [hN, Nat.cast_sub hqm.le]; push_cast; ring
  have hNne : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have htor := GlobalTheory.T.green_function_character_sum F θ m k (fun P => ∏ j, rootSum θ (e j) P) hm
  have horth := (GlobalTheory.CuspGL.torus_orthogonality F θ hθ m hm).2
  set T := {α : AlgebraicClosure F | α ^ N = 1} with hT
  have hTfin : T.Finite := by
    apply (Polynomial.nthRoots N (1 : AlgebraicClosure F)).toFinset.finite_toSet.subset
    intro α hα
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hN0).2 hα
  have key : ∀ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    intro α hα
    have hr : ∀ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a : Fin m, θ α ^ (e j * q ^ (a : ℕ)) :=
      fun j => (GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range F θ m (e j) α hm hα).trans (Finset.sum_range (fun a => θ α ^ (e j * q ^ a)))
    simp_rw [hr]
    rw [← Finset.mul_sum, ← star_sum, Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ᶠ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, ∑ᶠ α ∈ T, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    rw [finsum_mem_congr rfl key, finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hTfin]
  rw [hsum] at htor
  simp_rw [horth] at htor
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcast] at htor
  apply mul_left_cancel₀ hNne
  rw [htor]
  ring

end GlobalTheory.Shin
