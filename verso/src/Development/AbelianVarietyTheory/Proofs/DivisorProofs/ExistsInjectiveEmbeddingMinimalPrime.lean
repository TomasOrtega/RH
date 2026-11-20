import Mathlib
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Div

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_algHom_quotient_minimalPrime_injective (R K : Type) [CommRing R] [IsDomain R] [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K] (D : Type) [CommRing D] [Algebra R D] [Module.Flat R D] [Algebra.IsAlgebraic R D] (P : Ideal D) (hP : P ∈ minimalPrimes D) : ∃ em : D ⧸ P →ₐ[R] K, Function.Injective em := by
  haveI hPp : P.IsPrime := hP.1.1
  have hinj : Function.Injective (algebraMap R (D ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    have hreg : IsSMulRegular D r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h0)
    have hnz : algebraMap R D r ∈ nonZeroDivisors D := by
      rw [mem_nonZeroDivisors_iff_left]
      intro x hx
      apply hreg
      simp only [smul_zero]
      rw [Algebra.smul_def]; exact hx
    have hmem : algebraMap R D r ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) hmem hnz
  haveI : FaithfulSMul R (D ⧸ P) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective R K)
  haveI : Algebra.IsAlgebraic R (D ⧸ P) :=
    ⟨fun x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact (Algebra.IsAlgebraic.isAlgebraic (R := R) y).algHom (Ideal.Quotient.mkₐ R P)⟩
  haveI : Module.IsTorsionFree R (D ⧸ P) := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.IsTorsionFree R K := Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective R K)
  let f : D ⧸ P →ₐ[R] K := IsAlgClosed.lift
  refine ⟨f, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨y, r, hr, hy⟩ : ∃ y : D ⧸ P, ∃ r : R, r ≠ 0 ∧ x * y = algebraMap R _ r := by
    obtain ⟨r, hr, y, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) x).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
    exact ⟨y, r, hr, hy.symm⟩
  have := congrArg f hy
  rw [map_mul, hx, zero_mul, AlgHom.commutes] at this
  exact hr (IsFractionRing.injective R K (by rw [← this, map_zero]))

end GlobalTheory.Div
