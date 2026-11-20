import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open PrimeSpectrum in

/- English proof (translation)
Establish `hker : RingHom.ker χ ≤ Ideal.comap Polynomial.C P.asIdeal`. Introduce `a ha`. Establish `h1` using `congrArg PrimeSpectrum.asIdeal hP`. Simplify using `only [PrimeSpectrum.comap_asIdeal] at h1`. Establish `: a ∈ Ideal.comap (algebraMap R (Polynomial R)) P.asIdeal`.

Rewrite using `[h1, Ideal.mem_comap, RingHom.mem_ker.mp ha]`. Conclude with `Ideal.zero_mem _`. Conclude with `this`. Rewrite using `[range_comap_of_surjective _ _ (Polynomial.map_surjective χ hχ), PrimeSpectrum.mem_zeroLocus, Polynomial.ker_mapRingHom, SetLike.coe_subset_coe]`. Conclude with `Ideal.map_le_iff_le_comap.mpr hker`.
-/
theorem prime_line_mem_range_comap_mapRingHom {R K : Type} [CommRing R] [Field K] (χ : R →+* K)
    (hχ : Function.Surjective χ) (P : PrimeSpectrum (Polynomial R))
    (hP : PrimeSpectrum.comap (algebraMap R (Polynomial R)) P = PrimeSpectrum.comap χ (IsLocalRing.closedPoint K)) :
    P ∈ Set.range (PrimeSpectrum.comap (Polynomial.mapRingHom χ)) := by
  have hker : RingHom.ker χ ≤ Ideal.comap Polynomial.C P.asIdeal := by
    intro a ha
    have h1 := congrArg PrimeSpectrum.asIdeal hP
    simp only [PrimeSpectrum.comap_asIdeal] at h1
    have : a ∈ Ideal.comap (algebraMap R (Polynomial R)) P.asIdeal := by
      rw [h1, Ideal.mem_comap, RingHom.mem_ker.mp ha]
      exact Ideal.zero_mem _
    exact this
  rw [range_comap_of_surjective _ _ (Polynomial.map_surjective χ hχ), PrimeSpectrum.mem_zeroLocus,
    Polynomial.ker_mapRingHom, SetLike.coe_subset_coe]
  exact Ideal.map_le_iff_le_comap.mpr hker

/- English proof (translation)
Introduce `R K _ _ χ hχ x hx`. Conclude with `prime_line_mem_range_comap_mapRingHom χ hχ x hx`.
-/
theorem fibre_line_over_surjection : ∀ (R K : Type) [CommRing R] [Field K] (χ : R →+* K), Function.Surjective χ → ∀ (x : Sp (Polynomial R)), spMap (algebraMap R (Polynomial R)) x = spMap χ (IsLocalRing.closedPoint K) → x ∈ Set.range (spMap (Polynomial.mapRingHom χ)) := by
  intro R K _ _ χ hχ x hx
  exact prime_line_mem_range_comap_mapRingHom χ hχ x hx

end GlobalTheory
