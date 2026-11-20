import Mathlib

set_option autoImplicit false
noncomputable section
open IsLocalRing

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms

variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `r hr`. Assume the negation of the conclusion as `hnr`. Take `⟨u, hu⟩` from `hr`. Establish `hu' : χ r = ↑u` using `hu.symm`.

Establish `h1 : χ (r * algebraMap O R (↑u⁻¹ : O)) = 1`. Rewrite using `[map_mul, AlgHom.commutes, hu', Algebra.algebraMap_self, RingHom.id_apply, Units.mul_inv]`. Establish `h2 : IsUnit (1 - r * algebraMap O R (↑u⁻¹ : O))`. Apply `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits` to reduce the goal to its premises. Conclude with `mul_mem_nonunits_left hnr`.

Establish `h3 : χ (1 - r * algebraMap O R (↑u⁻¹ : O)) = 0` using `by rw [map_sub, map_one, h1, sub_self]`. Establish `h4` using `h2.map χ`. Rewrite `h4` using `[h3]`. Conclude with `not_isUnit_zero h4`.
-/
theorem isLocalHom_of_section (χ : R →ₐ[O] O) : IsLocalHom (χ : R →+* O) := by
  constructor
  intro r hr
  by_contra hnr
  obtain ⟨u, hu⟩ := hr
  have hu' : χ r = ↑u := hu.symm
  have h1 : χ (r * algebraMap O R (↑u⁻¹ : O)) = 1 := by
    rw [map_mul, AlgHom.commutes, hu', Algebra.algebraMap_self, RingHom.id_apply, Units.mul_inv]
  have h2 : IsUnit (1 - r * algebraMap O R (↑u⁻¹ : O)) := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact mul_mem_nonunits_left hnr
  have h3 : χ (1 - r * algebraMap O R (↑u⁻¹ : O)) = 0 := by rw [map_sub, map_one, h1, sub_self]
  have h4 := h2.map χ
  rw [h3] at h4
  exact not_isUnit_zero h4

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a ha`. Assume the negation of the conclusion as `hna`. Establish `hmax : (Ideal.comap (algebraMap O R) (maximalIdeal R)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R)`. Establish `heq : Ideal.comap (algebraMap O R) (maximalIdeal R) = maximalIdeal O` using `IsLocalRing.eq_maximalIdeal hmax`.

Establish `h1 : a ∈ Ideal.comap (algebraMap O R) (maximalIdeal R)`. Rewrite using `[heq]`. Conclude with `hna`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h1)) ha`.
-/
theorem isLocalHom_algebraMap [Module.Finite O R] : IsLocalHom (algebraMap O R) := by
  constructor
  intro a ha
  by_contra hna
  have hmax : (Ideal.comap (algebraMap O R) (maximalIdeal R)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R)
  have heq : Ideal.comap (algebraMap O R) (maximalIdeal R) = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hmax
  have h1 : a ∈ Ideal.comap (algebraMap O R) (maximalIdeal R) := by
    rw [heq]
    exact hna
  exact ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h1)) ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `r hr`. Assume the negation of the conclusion as `hnr`. Establish `hcomap : Ideal.comap (algebraMap O R) (Ideal.comap (χ : R →+* S) (maximalIdeal S)) = maximalIdeal O`. Rewrite using `[Ideal.comap_comap, AlgHom.comp_algebraMap]`.

Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]`. Conclude with `⟨fun h ha => h (ha.map _), fun h ha => h (hS.map_nonunit a ha)⟩`. Establish `hmax : (Ideal.comap (χ : R →+* S) (maximalIdeal S)).IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hcomap]; infer_instance)`. Establish `hPeq : Ideal.comap (χ : R →+* S) (maximalIdeal S) = maximalIdeal R` using `IsLocalRing.eq_maximalIdeal hmax`.

Establish `hrP : r ∈ Ideal.comap (χ : R →+* S) (maximalIdeal S)`. Rewrite using `[hPeq]`. Conclude with `hnr`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hrP) hr`.
-/
theorem isLocalHom_of_finite [Module.Finite O R] {S : Type} [CommRing S] [IsLocalRing S] [Algebra O S]
    (hS : IsLocalHom (algebraMap O S)) (χ : R →ₐ[O] S) : IsLocalHom (χ : R →+* S) := by
  constructor
  intro r hr
  by_contra hnr
  have hcomap : Ideal.comap (algebraMap O R) (Ideal.comap (χ : R →+* S) (maximalIdeal S)) = maximalIdeal O := by
    rw [Ideal.comap_comap, AlgHom.comp_algebraMap]
    ext a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    exact ⟨fun h ha => h (ha.map _), fun h ha => h (hS.map_nonunit a ha)⟩
  have hmax : (Ideal.comap (χ : R →+* S) (maximalIdeal S)).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hcomap]; infer_instance)
  have hPeq : Ideal.comap (χ : R →+* S) (maximalIdeal S) = maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  have hrP : r ∈ Ideal.comap (χ : R →+* S) (maximalIdeal S) := by
    rw [hPeq]
    exact hnr
  exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hrP) hr

end ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
