import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_unit_norm_eq_of_algHom : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] [IsReduced A] (ψ : A →ₐ[K] K) (c : K), c ≠ 0 → ∃ y : Aˣ, Algebra.norm K (y : A) = c := by
  intro K A _ _ _ _ _ ψ c hc
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker ψ)
  have he0 : ψ e = 0 := by
    have : e ∈ RingHom.ker ψ := by rw [hI]; exact Ideal.subset_span rfl
    exact this
  set f : A := 1 - e with hf
  have hψf : ψ f = 1 := by simp [hf, he0]
  have hmul : ∀ a : A, f * a = ψ a • f := by
    intro a
    have h1 : a - algebraMap K A (ψ a) ∈ RingHom.ker ψ := by
      simp [RingHom.mem_ker]
    rw [hI, Ideal.mem_span_singleton'] at h1
    obtain ⟨b, hb⟩ := h1
    have h2 : f * (b * e) = 0 := by
      have : e * e = e := he
      rw [hf]; linear_combination (-b) * this
    rw [hb, mul_sub, sub_eq_zero] at h2
    rw [h2, Algebra.smul_def, mul_comm]
  have hff : f * f = f := by rw [hmul, hψf, one_smul]
  have hinv : (1 + (c - 1) • f) * (1 + (c⁻¹ - 1) • f) = 1 := by
    have : (c⁻¹ - 1) + (c - 1) + (c - 1) * (c⁻¹ - 1) = 0 := by field_simp; ring
    rw [mul_add, add_mul, add_mul, smul_mul_smul_comm, hff]
    simp only [one_mul, mul_one]
    rw [add_assoc, ← add_smul, ← add_smul]
    have h3 : c - 1 + (c⁻¹ - 1 + (c - 1) * (c⁻¹ - 1)) = 0 := by linear_combination this
    rw [h3]; simp
  refine ⟨⟨1 + (c - 1) • f, 1 + (c⁻¹ - 1) • f, hinv, by rw [mul_comm, hinv]⟩, ?_⟩
  rw [Algebra.norm_apply]
  have hT : LinearMap.mul K A (1 + (c - 1) • f) = LinearMap.transvection ψ.toLinearMap ((c - 1) • f) := by
    ext a
    simp [LinearMap.transvection.apply, hmul, smul_smul, mul_comm]
  change LinearMap.det (LinearMap.mul K A (1 + (c - 1) • f)) = c
  rw [hT, LinearMap.transvection.det]
  simp [hψf]

end GlobalTheory.CNorm
