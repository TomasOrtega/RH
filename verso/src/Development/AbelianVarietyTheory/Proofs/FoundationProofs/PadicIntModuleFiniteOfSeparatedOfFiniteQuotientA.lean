import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

namespace GlobalTheory

/- English proof (translation)
Establish `hI : IsLocalRing.maximalIdeal ℤ_[l] = Ideal.span {(l : ℤ_[l])}` using `PadicInt.maximalIdeal_eq_span_p`. Establish `: IsHausdorff (IsLocalRing.maximalIdeal ℤ_[l]) X`. Use `⟨fun x hx => hsep x fun r => ?_⟩` and prove the remaining obligations. Establish `h` using `hx r`. Rewrite `h` using `[SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`.

Take `⟨y, -, hy⟩` from `h`. Conclude with `⟨y, hy⟩`. Establish `hE : (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X) = LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1))`. Use extensionality with `x`. Rewrite using `[hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`.

Simplify using `[LinearMap.mem_range]`. Establish `: Module.Finite ℤ_[l] (X ⧸ (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X))`. Rewrite using `[hE]`. Conclude with `Module.Finite.of_finite`. Conclude with `finite_of_isHausdorff_of_finite_quotient (IsLocalRing.maximalIdeal ℤ_[l]) X`.
-/
theorem padicInt_module_finite_of_separated_of_finite_quotient (l : ℕ) [Fact l.Prime] (X : Type)
    [AddCommGroup X] [Module ℤ_[l] X]
    (hfin : Finite (X ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1))))
    (hsep : ∀ x : X, (∀ r : ℕ, ∃ y, (l : ℤ_[l]) ^ r • y = x) → x = 0) :
    Module.Finite ℤ_[l] X := by
  have hI : IsLocalRing.maximalIdeal ℤ_[l] = Ideal.span {(l : ℤ_[l])} :=
    PadicInt.maximalIdeal_eq_span_p
  have : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[l]) X := by
    refine ⟨fun x hx => hsep x fun r => ?_⟩
    have h := hx r
    rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨y, -, hy⟩ := h
    exact ⟨y, hy⟩
  have hE : (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X) =
      LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1)) := by
    ext x
    rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp [LinearMap.mem_range]
  have : Module.Finite ℤ_[l] (X ⧸ (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X)) := by
    rw [hE]
    exact Module.Finite.of_finite
  exact finite_of_isHausdorff_of_finite_quotient (IsLocalRing.maximalIdeal ℤ_[l]) X

end GlobalTheory
