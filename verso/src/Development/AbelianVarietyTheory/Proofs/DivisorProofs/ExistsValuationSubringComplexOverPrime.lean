import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

/- English proof (translation)
Introduce `F _ w`. Use `set R := w.valuationSubringAtPrime F with hR`. Take `⟨V, hV, hloc⟩` from `IsLocalRing.exists_factor_valuationRing ((algebraMap F ℂ).comp R.subtype)`. Use `⟨V, fun x => ⟨fun hx => ?_, fun hx => hV ⟨x, hx⟩⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hxR`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hxR R.zero_mem`. Establish `hinv : x⁻¹ ∈ R` using `(R.mem_or_inv_mem x).resolve_left hxR`. Establish `hx0' : (x : ℂ) ≠ 0` using `by exact_mod_cast hx0`.

Establish `hu : IsUnit ((((algebraMap F ℂ).comp R.subtype).codRestrict V.toSubring hV) ⟨x⁻¹, hinv⟩)`. Use `IsUnit.of_mul_eq_one ⟨(x : ℂ), hx⟩ ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((x⁻¹ : F) : ℂ) * (x : ℂ) = 1`. Rewrite using `[IntermediateField.coe_inv, inv_mul_cancel₀ hx0']`.

Establish `hu' : IsUnit (⟨x⁻¹, hinv⟩ : R)` using `hloc.map_nonunit _ hu`. Take `⟨y, hy⟩` from `hu'.exists_right_inv`. Establish `hy' : x⁻¹ * (y : F) = 1` using `congrArg Subtype.val hy`. Establish `: x = (y : F)`. Establish `h` using `congrArg (x * ·) hy'`.

Simplify using `only [← mul_assoc, mul_inv_cancel₀ hx0, one_mul, mul_one] at h`. Conclude with `h.symm`. Conclude with `hxR (this ▸ y.2)`.
-/
theorem exists_valuationSubring_complex_over_prime :
    ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)),
      ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  intro F _ w
  set R := w.valuationSubringAtPrime F with hR
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing
    ((algebraMap F ℂ).comp R.subtype)
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hV ⟨x, hx⟩⟩⟩
  by_contra hxR
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxR R.zero_mem
  have hinv : x⁻¹ ∈ R := (R.mem_or_inv_mem x).resolve_left hxR
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hu : IsUnit ((((algebraMap F ℂ).comp R.subtype).codRestrict V.toSubring hV) ⟨x⁻¹, hinv⟩) := by
    refine IsUnit.of_mul_eq_one ⟨(x : ℂ), hx⟩ ?_
    apply Subtype.ext
    change ((x⁻¹ : F) : ℂ) * (x : ℂ) = 1
    rw [IntermediateField.coe_inv, inv_mul_cancel₀ hx0']
  have hu' : IsUnit (⟨x⁻¹, hinv⟩ : R) := hloc.map_nonunit _ hu
  obtain ⟨y, hy⟩ := hu'.exists_right_inv
  have hy' : x⁻¹ * (y : F) = 1 := congrArg Subtype.val hy
  have : x = (y : F) := by
    have h := congrArg (x * ·) hy'
    simp only [← mul_assoc, mul_inv_cancel₀ hx0, one_mul, mul_one] at h
    exact h.symm
  exact hxR (this ▸ y.2)

end GlobalTheory.CMModel
