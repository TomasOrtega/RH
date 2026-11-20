import Mathlib

namespace GroundTheory.Global

open NumberField IsDedekindDomain Polynomial

noncomputable section

variable (L : Type*) [Field L] [NumberField L]

def localizationAt (v : HeightOneSpectrum (𝓞 L)) : Subalgebra (𝓞 L) L :=
  Localization.subalgebra.ofField L v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors

variable {L}

instance (v : HeightOneSpectrum (𝓞 L)) : IsLocalization.AtPrime (localizationAt L v) v.asIdeal :=
  Localization.subalgebra.isLocalization_ofField _ _ _

instance (v : HeightOneSpectrum (𝓞 L)) : IsDiscreteValuationRing (localizationAt L v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) v.ne_bot _

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mem_localizationAt_iff {v : HeightOneSpectrum (𝓞 L)} {x : L} :
    x ∈ localizationAt L v ↔ ∃ a s : 𝓞 L, s ∉ v.asIdeal ∧
      x = algebraMap (𝓞 L) L a * (algebraMap (𝓞 L) L s)⁻¹ := by
  unfold localizationAt Localization.subalgebra.ofField
  rw [← SetLike.mem_coe, Subalgebra.coe_copy]
  simp only [Set.mem_ofPred_eq, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_compl_iff, SetLike.mem_coe, exists_prop]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_setOf_mem_asIdeal {b : 𝓞 L} (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 L) | b ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (I := Ideal.span {b}) (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])).subset
    fun _ hv => Ideal.dvd_span_singleton.mpr hv

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem eventually_mem_localizationAt (x : L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, x ∈ localizationAt L v := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  refine Filter.eventually_cofinite.mpr
    ((finite_setOf_mem_asIdeal (nonZeroDivisors.ne_zero hb)).subset fun v hv => ?_)
  by_contra h
  exact hv (mem_localizationAt_iff.mpr ⟨a, b, h, div_eq_mul_inv _ _⟩)

omit [NumberField L] in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isUnit_of_mem_of_inv_mem {R : Type*} [CommRing R] [Algebra R L] {S : Subalgebra R L}
    {x : L} (hx : x ≠ 0) (h : x ∈ S) (h' : x⁻¹ ∈ S) : IsUnit (⟨x, h⟩ : S) :=
  isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, h'⟩, Subtype.ext (mul_inv_cancel₀ hx)⟩

/- English proof (translation)
Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem eventually_isUnit_localizationAt {x : L} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ h : x ∈ localizationAt L v, IsUnit (⟨x, h⟩ : localizationAt L v) := by
  filter_upwards [eventually_mem_localizationAt x, eventually_mem_localizationAt x⁻¹] with v h h'
  exact ⟨h, isUnit_of_mem_of_inv_mem hx h h'⟩

end

end GroundTheory.Global
