import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Introduce `K A _ _ _ _ _ ψ c hc`. Establish `: IsArtinianRing A` using `IsArtinianRing.of_finite K A`. Establish `: IsSemisimpleRing A` using `IsArtinianRing.isSemisimpleRing_of_isReduced A`. Take `⟨e, he, hI⟩` from `IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker ψ)`. Establish `he0 : ψ e = 0`.

Establish `: e ∈ RingHom.ker ψ` using `by rw [hI]; exact Ideal.subset_span rfl`. Conclude with `this`. Use `set f : A := 1 - e with hf`. Establish `hψf : ψ f = 1` using `by simp [hf, he0]`. Establish `hmul : ∀ a : A, f * a = ψ a • f`.

Introduce `a`. Establish `h1 : a - algebraMap K A (ψ a) ∈ RingHom.ker ψ`. Simplify using `[RingHom.mem_ker]`. Rewrite `h1` using `[hI, Ideal.mem_span_singleton']`. Take `⟨b, hb⟩` from `h1`.

Establish `h2 : f * (b * e) = 0`. Establish `: e * e = e` using `he`. Rewrite using `[hf]`. Take the linear combination `(-b) * this`. Rewrite `h2` using `[hb, mul_sub, sub_eq_zero]`.

Rewrite using `[h2, Algebra.smul_def, mul_comm]`. Establish `hff : f * f = f` using `by rw [hmul, hψf, one_smul]`. Establish `hinv : (1 + (c - 1) • f) * (1 + (c⁻¹ - 1) • f) = 1`. Establish `: (c⁻¹ - 1) + (c - 1) + (c - 1) * (c⁻¹ - 1) = 0` using `by field_simp; ring`. Rewrite using `[mul_add, add_mul, add_mul, smul_mul_smul_comm, hff]`.

Simplify using `only [one_mul, mul_one]`. Rewrite using `[add_assoc, ← add_smul, ← add_smul]`. Establish `h3 : c - 1 + (c⁻¹ - 1 + (c - 1) * (c⁻¹ - 1)) = 0` using `by linear_combination this`. Rewrite using `[h3]`. Simplify using the standard rewrite rules.

Use `⟨⟨1 + (c - 1) • f, 1 + (c⁻¹ - 1) • f, hinv, by rw [mul_comm, hinv]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.norm_apply]`. Establish `hT : LinearMap.mul K A (1 + (c - 1) • f) = LinearMap.transvection ψ.toLinearMap ((c - 1) • f)`. Use extensionality with `a`. Simplify using `[LinearMap.transvection.apply, hmul, smul_smul, mul_comm]`.

Express the relevant statement in the definitionally equal form `LinearMap.det (LinearMap.mul K A (1 + (c - 1) • f)) = c`. Rewrite using `[hT, LinearMap.transvection.det]`. Simplify using `[hψf]`.
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
