import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Establish `hint : IsIntegral R a` using `Algebra.IsIntegral.isIntegral a`. Establish `halg : IsAlgebraic R a` using `hint.isAlgebraic`. Take `⟨c, hc, a', hca⟩` from `halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)`. Establish `hc0 : c ≠ 0`. Conclude with `hc`.

Establish `key : c • x = 0`. Establish `h1 : ρ (algebraMap R Λ c) = c • (1 : Matrix (Fin h) (Fin h) R)`. Rewrite using `[AlgHom.commutes, Algebra.algebraMap_eq_smul_one]`. Establish `h2 : (ρ (algebraMap R Λ c)).mulVec x = c • x`. Rewrite using `[h1, Matrix.smul_mulVec, Matrix.one_mulVec]`.

Rewrite using `[← h2, hca, mul_comm, map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]`. Use function extensionality and compare the values at `i`. Establish `hi : c * x i = 0` using `by simpa using congrFun key i`. Simplify `hi` using `[hc0]`.
-/
theorem torsionFree_of_finite_domain_action
    (R Λ : Type) [CommRing R] [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ]
    [Module.Finite R Λ] [FaithfulSMul R Λ] (h : ℕ)
    (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) R) (a : Λ) (x : Fin h → R)
    (ha : a ≠ 0) (hx : (ρ a).mulVec x = 0) : x = 0 := by
  have hint : IsIntegral R a := Algebra.IsIntegral.isIntegral a
  have halg : IsAlgebraic R a := hint.isAlgebraic
  obtain ⟨c, hc, a', hca⟩ := halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
  have hc0 : c ≠ 0 := by
    exact hc
  have key : c • x = 0 := by
    have h1 : ρ (algebraMap R Λ c) = c • (1 : Matrix (Fin h) (Fin h) R) := by
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    have h2 : (ρ (algebraMap R Λ c)).mulVec x = c • x := by
      rw [h1, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← h2, hca, mul_comm, map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  funext i
  have hi : c * x i = 0 := by simpa using congrFun key i
  simpa [hc0] using hi

/- English proof (translation)
Introduce `R Λ _ _ _ _ _ _ _ h ρ a x ha hx` and use `torsionFree_of_finite_domain_action R Λ h ρ a x ha hx`.
-/
theorem torsionFree_of_finite_domain_action' :
    ∀ (R Λ : Type) [CommRing R] [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ] [Module.Finite R Λ] [FaithfulSMul R Λ] (h : ℕ) (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) R) (a : Λ) (x : Fin h → R), a ≠ 0 → (ρ a).mulVec x = 0 → x = 0 :=
  fun R Λ _ _ _ _ _ _ _ h ρ a x ha hx => torsionFree_of_finite_domain_action R Λ h ρ a x ha hx

end GlobalTheory
