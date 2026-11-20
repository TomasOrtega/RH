import Mathlib
import Formalism.PeriodIntegrals.LocBasisPlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalBasisAtPrime.SpanClear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalBasisAtPrime.MemPrimeComplIff

open NumberField

namespace LocBasisPlaceWork

/- English proof (translation)
Introduce `E _ _ p _ ρ N L hL hsp`. Set `A` to `Localization.AtPrime (plc ρ)`. Establish `hle : (plc ρ).primeCompl ≤ nonZeroDivisors (𝓞 E)` using `Ideal.primeCompl_le_nonZeroDivisors (plc ρ)`. Use `letI : Algebra A E := IsLocalization.localizationAlgebraOfSubmonoidLe A E (plc ρ).primeCompl (nonZeroDivisors (𝓞 E)) hle`. Establish `: IsScalarTower (𝓞 E) A E` using `IsLocalization.localization_isScalarTower_of_submonoid_le A E (plc ρ).primeCompl (nonZeroDivisors (𝓞 E)) hle`.

Establish `: IsDomain A` using `IsLocalization.isDomain_localization hle`. Establish `: IsFractionRing A E` using `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (plc ρ).primeCompl A E`. Establish `: IsDiscreteValuationRing A` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) (plc_ne_bot ρ) A`. Take `⟨P, hdet, hcol, hx⟩` from `core (A := A) (plc ρ).primeCompl N L hL hsp`. Use `⟨P, hdet, fun a => ?_, fun x hxL => ?_⟩` and prove the remaining obligations.

Take `⟨s, hs, h⟩` from `hcol a`. Conclude with `⟨s, (mem_primeCompl_iff ρ s).mp hs, h⟩`. Take `⟨s, hs, c, h⟩` from `hx x hxL`. Conclude with `⟨s, (mem_primeCompl_iff ρ s).mp hs, c, h⟩`.
-/
theorem main : PI.LocBasisPlace := by
  intro E _ _ p _ ρ N L hL hsp
  let A := Localization.AtPrime (plc ρ)
  have hle : (plc ρ).primeCompl ≤ nonZeroDivisors (𝓞 E) :=
    Ideal.primeCompl_le_nonZeroDivisors (plc ρ)
  letI : Algebra A E :=
    IsLocalization.localizationAlgebraOfSubmonoidLe A E (plc ρ).primeCompl
      (nonZeroDivisors (𝓞 E)) hle
  have : IsScalarTower (𝓞 E) A E :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A E (plc ρ).primeCompl
      (nonZeroDivisors (𝓞 E)) hle
  have : IsDomain A := IsLocalization.isDomain_localization hle
  have : IsFractionRing A E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (plc ρ).primeCompl A E
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) (plc_ne_bot ρ) A
  obtain ⟨P, hdet, hcol, hx⟩ := core (A := A) (plc ρ).primeCompl N L hL hsp
  refine ⟨P, hdet, fun a => ?_, fun x hxL => ?_⟩
  · obtain ⟨s, hs, h⟩ := hcol a
    exact ⟨s, (mem_primeCompl_iff ρ s).mp hs, h⟩
  · obtain ⟨s, hs, c, h⟩ := hx x hxL
    exact ⟨s, (mem_primeCompl_iff ρ s).mp hs, c, h⟩

end LocBasisPlaceWork
