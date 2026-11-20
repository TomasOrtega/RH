import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Take `⟨p, hp, hI⟩` from `Ideal.exists_le_maximal (Ideal.span {a}).annihilator fun h => h0 ((one_smul A a).symm.trans ((Submodule.mem_annihilator_span_singleton a 1).1 (h ▸ Submodule.mem_top)))`. Take `⟨f, hf, n, _, _, _⟩` from `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)`. Set `P` to `MvPolynomial (Fin n) K`.

Establish `: IsReduced (TensorProduct P (FractionRing P) (Localization.Away f))` using `Algebra.FormallyUnramified.isReduced_of_field (FractionRing P) _`. Establish `: IsReduced (Localization.Away f)` using `isReduced_of_injective _ (Algebra.TensorProduct.includeRight_injective (A := FractionRing P) (IsFractionRing.injective P _))`. Take `⟨⟨_, N, rfl⟩, hN⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) a).1 (ha.map (algebraMap A (Localization.Away f))).eq_zero`. Conclude with `hf (hp.isPrime.mem_of_pow_mem N (hI ((Submodule.mem_annihilator_span_singleton a _).2 hN)))`.
-/
theorem isReduced_of_smooth_over_field (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] : IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  by_contra h0
  obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal (Ideal.span {a}).annihilator fun h =>
    h0 ((one_smul A a).symm.trans ((Submodule.mem_annihilator_span_singleton a 1).1 (h ▸ Submodule.mem_top)))
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  have : IsReduced (TensorProduct P (FractionRing P) (Localization.Away f)) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing P) _
  have : IsReduced (Localization.Away f) := isReduced_of_injective _
    (Algebra.TensorProduct.includeRight_injective (A := FractionRing P) (IsFractionRing.injective P _))
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) a).1
    (ha.map (algebraMap A (Localization.Away f))).eq_zero
  exact hf (hp.isPrime.mem_of_pow_mem N (hI ((Submodule.mem_annihilator_span_singleton a _).2 hN)))

end GlobalTheory
