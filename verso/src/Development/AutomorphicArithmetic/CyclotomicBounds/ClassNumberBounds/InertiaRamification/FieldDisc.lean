import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDefs

namespace KStar.Ram

open NumberField
open scoped Pointwise

variable (E : Type*) [Field E] [NumberField E]

/- English proof (translation)
Rewrite using `[← Submodule.mem_div_iff_forall_mul_mem, ← coeSubmodule_differentIdeal ℤ ℚ (L := E) (𝓞 E), IsLocalization.mem_coeSubmodule]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨x, h, rfl⟩`. Introduce and unpack `⟨y, hy, h⟩`.

Establish `: y = x` using `FaithfulSMul.algebraMap_injective (𝓞 E) E h`. Conclude with `this ▸ hy`.
-/
private theorem mem_differentIdeal_iff' (x : 𝓞 E) :
    x ∈ differentIdeal ℤ (𝓞 E) ↔
      ∀ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E), (x : E) * y ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← Submodule.mem_div_iff_forall_mul_mem, ← coeSubmodule_differentIdeal ℤ ℚ (L := E) (𝓞 E),
    IsLocalization.mem_coeSubmodule]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, h⟩
    have : y = x := FaithfulSMul.algebraMap_injective (𝓞 E) E h
    exact this ▸ hy

/- English proof (translation)
Establish `hone : ∀ (τ : Gal(E/ℚ)) (a : E), a ∈ (1 : Submodule (𝓞 E) E) → τ a ∈ (1 : Submodule (𝓞 E) E)`. Introduce `τ a ha`. Rewrite `ha`, the goal using `[Submodule.mem_one]`. Take `⟨b, rfl⟩` from `ha`. Conclude with `⟨τ • b, rfl⟩`.

Rewrite `hx`, the goal using `[mem_differentIdeal_iff']`. Introduce `y hy`. Establish `hy' : σ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)`. Rewrite `hy`, the goal using `[Submodule.mem_traceDual]`. Introduce `a ha`.

Use `hy (σ a) (hone σ a ha)` as an intermediate fact. Rewrite `this`, the goal using `[Algebra.traceForm_apply]`. Rewrite using `[← Algebra.trace_eq_of_algEquiv σ, map_mul, AlgEquiv.apply_symm_apply]`. Conclude with `this`. Use `hone σ _ (hx _ hy')` as an intermediate fact.

Rewrite `this` using `[map_mul, AlgEquiv.apply_symm_apply]`. Conclude with `this`.
-/
private theorem smul_mem_differentIdeal' (σ : Gal(E/ℚ)) {x : 𝓞 E}
    (hx : x ∈ differentIdeal ℤ (𝓞 E)) : σ • x ∈ differentIdeal ℤ (𝓞 E) := by
  have hone : ∀ (τ : Gal(E/ℚ)) (a : E), a ∈ (1 : Submodule (𝓞 E) E) →
      τ a ∈ (1 : Submodule (𝓞 E) E) := by
    intro τ a ha
    rw [Submodule.mem_one] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    exact ⟨τ • b, rfl⟩
  rw [mem_differentIdeal_iff'] at hx ⊢
  intro y hy
  have hy' : σ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    have := hy (σ a) (hone σ a ha)
    rw [Algebra.traceForm_apply] at this ⊢
    rw [← Algebra.trace_eq_of_algEquiv σ, map_mul, AlgEquiv.apply_symm_apply]
    exact this
  have := hone σ _ (hx _ hy')
  rw [map_mul, AlgEquiv.apply_symm_apply] at this
  exact this

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using smul_mem_differentIdeal' E σ h`.

Conclude with `smul_mem_differentIdeal' E σ⁻¹`.
-/
theorem smul_differentIdeal (σ : Gal(E/ℚ)) :
    σ • differentIdeal ℤ (𝓞 E) = differentIdeal ℤ (𝓞 E) := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro h
    simpa using smul_mem_differentIdeal' E σ h
  · exact smul_mem_differentIdeal' E σ⁻¹

end KStar.Ram
