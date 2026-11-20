import Mathlib

noncomputable section

namespace PI.CntNotIntW

open scoped TensorProduct

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem trace_of_ker {Q A B : Type*} [Field Q] [CommRing A] [Algebra Q A] [FiniteDimensional Q A]
    [Field B] [Algebra Q B] [FiniteDimensional Q B] (π : A →ₐ[Q] B) (hπ : Function.Surjective π)
    (a : A) (ha : ∀ x, π x = 0 → a * x = 0) : Algebra.trace Q A a = Algebra.trace Q B (π a) := by
  classical
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective π.toLinearMap
    (LinearMap.range_eq_top.mpr hπ)
  have hsy : ∀ y, π (s y) = y := fun y => LinearMap.congr_fun hs y

  have hL : Algebra.lmul Q A a = (Algebra.lmul Q A a ∘ₗ s) ∘ₗ π.toLinearMap := by
    ext x
    have hk : π (x - s (π x)) = 0 := by rw [map_sub, hsy, sub_self]
    have h := ha _ hk
    rw [mul_sub, sub_eq_zero] at h
    simpa using h
  rw [Algebra.trace_apply, Algebra.trace_apply, hL, LinearMap.trace_comp_comm']
  congr 1
  ext y
  simp [hsy]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem trace_one_tmul {Q K : Type*} [Field Q] [Algebra ℚ Q] [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (y : K) : Algebra.trace Q (Q ⊗[ℚ] K) (1 ⊗ₜ y) = algebraMap ℚ Q (Algebra.trace ℚ K y) := by
  rw [Algebra.trace_apply, Algebra.trace_apply]
  have h : Algebra.lmul Q (Q ⊗[ℚ] K) (1 ⊗ₜ y) = (Algebra.lmul ℚ K y).baseChange Q := by
    ext k
    simp
  rw [h, LinearMap.trace_baseChange]

end PI.CntNotIntW
