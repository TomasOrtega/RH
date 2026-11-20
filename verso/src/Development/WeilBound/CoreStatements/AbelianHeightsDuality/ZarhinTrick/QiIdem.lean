import Mathlib
import PositivityTheory.PublishedTheorems.WeilRepresentations.ZariskiDensity.QiCoreDefs

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hne1 : Ideal.span {1 - f} ≠ ⊤`. Introduce `htop`. Rewrite `htop` using `[Ideal.span_singleton_eq_top]`. Apply `hne` to reduce the goal to its premises.

Establish `h0 : f * (1 - f) = 0` using `by rw [mul_sub, mul_one, hf.eq, sub_self]`. Conclude with `htop.mul_left_eq_zero.1 h0`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne1`. Use `letI := Ideal.Quotient.field M`. Use `haveI : Module.Finite K (H ⧸ M) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)`.

Use `haveI : Algebra.IsIntegral K (H ⧸ M) := Algebra.IsIntegral.of_finite K (H ⧸ M)`. Establish `hb` using `IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := H ⧸ M)`. Set `e : K ≃ₐ[K] H ⧸ M` to `AlgEquiv.ofBijective (Algebra.ofId K (H ⧸ M)) hb`. Set `x : H →ₐ[K] K` to `e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M)`. Establish `h1 : Ideal.Quotient.mk M f = 1`.

Establish `hmem : 1 - f ∈ M` using `hle (Ideal.mem_span_singleton_self _)`. Establish `h2 : Ideal.Quotient.mk M (1 - f) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hmem`. Rewrite `h2` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `h2.symm`. Establish `hx1 : x f = 1`.

Express the relevant statement in the definitionally equal form `e.symm (Ideal.Quotient.mkₐ K M f) = 1`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, h1, map_one]`. Establish `hx` using `h x`. Rewrite `hx` using `[hx1]`. Conclude with `one_ne_zero hx`.
-/
theorem idem_eq_zero {K H : Type} [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    {f : H} (hf : IsIdempotentElem f) (h : ∀ x : H →ₐ[K] K, x f = 0) : f = 0 := by
  by_contra hne
  have hne1 : Ideal.span {1 - f} ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    apply hne
    have h0 : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hf.eq, sub_self]
    exact htop.mul_left_eq_zero.1 h0
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne1
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (H ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  haveI : Algebra.IsIntegral K (H ⧸ M) := Algebra.IsIntegral.of_finite K (H ⧸ M)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := H ⧸ M)
  let e : K ≃ₐ[K] H ⧸ M := AlgEquiv.ofBijective (Algebra.ofId K (H ⧸ M)) hb
  let x : H →ₐ[K] K := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M)
  have h1 : Ideal.Quotient.mk M f = 1 := by
    have hmem : 1 - f ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : Ideal.Quotient.mk M (1 - f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  have hx1 : x f = 1 := by
    change e.symm (Ideal.Quotient.mkₐ K M f) = 1
    rw [Ideal.Quotient.mkₐ_eq_mk, h1, map_one]
  have hx := h x
  rw [hx1] at hx
  exact one_ne_zero hx

end PositivityTheory.PrwZar.Qi
