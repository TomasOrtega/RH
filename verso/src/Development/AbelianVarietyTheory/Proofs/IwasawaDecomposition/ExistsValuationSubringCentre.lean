import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocToFracAlgebraMap
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.LocM.Lift

/- English proof (translation)
Take `⟨V, hle⟩` from `(LocalSubring.range (locToFrac P)).exists_le_valuationSubring`. Take `⟨h1, h2⟩` from `hle`. Establish `hV : ∀ x, locToFrac P x ∈ V` using `fun x => h1 ⟨x, rfl⟩`. Set `g : Localization.AtPrime P →+* V` to `(locToFrac P).codRestrict V hV`. Establish `hg : IsLocalHom g`.

Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Establish `hr : IsLocalHom (locToFrac P).rangeRestrict` using `.of_surjective _ (locToFrac P).rangeRestrict_surjective`. Use `hr.1 x (h2.1 ⟨locToFrac P x, x, rfl⟩ ?_)` and prove the remaining obligations. Take `⟨⟨y, hy⟩, e⟩` from `isUnit_iff_exists_inv.mp hx`. Conclude with `isUnit_iff_exists_inv.mpr ⟨⟨y, hy⟩, Subtype.ext congr(($e).1)⟩`.

Use `⟨V, g.comp (algebraMap R (Localization.AtPrime P)), ?_, fun r hr => ?_, fun r hr => ?_⟩` and prove the remaining obligations. Use extensionality with `r`. Conclude with `locToFrac_algebraMap P r`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`.

Use `(isUnit_map_iff g _).mp hu` as an intermediate fact. Establish `hm : algebraMap R (Localization.AtPrime P) r ∈ IsLocalRing.maximalIdeal _`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`. Conclude with `Ideal.mem_map_of_mem _ hr`. Conclude with `hm this`.

Conclude with `(IsLocalization.map_units (Localization.AtPrime P) (⟨r, hr⟩ : P.primeCompl)).map g`.
-/
theorem exists_valuationSubring_centre (R : Type) [CommRing R] [IsDomain R] (P : Ideal R)
    [P.IsPrime] :
    ∃ (V : ValuationSubring (FractionRing R)) (ι : R →+* V),
      V.subtype.comp ι = algebraMap R (FractionRing R) ∧
      (∀ r ∈ P, ι r ∈ IsLocalRing.maximalIdeal V) ∧ ∀ r ∉ P, IsUnit (ι r) := by
  obtain ⟨V, hle⟩ := (LocalSubring.range (locToFrac P)).exists_le_valuationSubring
  obtain ⟨h1, h2⟩ := hle
  have hV : ∀ x, locToFrac P x ∈ V := fun x => h1 ⟨x, rfl⟩
  let g : Localization.AtPrime P →+* V := (locToFrac P).codRestrict V hV
  have hg : IsLocalHom g := by
    refine ⟨fun x hx => ?_⟩
    have hr : IsLocalHom (locToFrac P).rangeRestrict :=
      .of_surjective _ (locToFrac P).rangeRestrict_surjective
    refine hr.1 x (h2.1 ⟨locToFrac P x, x, rfl⟩ ?_)
    obtain ⟨⟨y, hy⟩, e⟩ := isUnit_iff_exists_inv.mp hx
    exact isUnit_iff_exists_inv.mpr ⟨⟨y, hy⟩, Subtype.ext congr(($e).1)⟩
  refine ⟨V, g.comp (algebraMap R (Localization.AtPrime P)), ?_, fun r hr => ?_, fun r hr => ?_⟩
  · ext r
    exact locToFrac_algebraMap P r
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (isUnit_map_iff g _).mp hu
    have hm : algebraMap R (Localization.AtPrime P) r ∈ IsLocalRing.maximalIdeal _ := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hr
    exact hm this
  · exact (IsLocalization.map_units (Localization.AtPrime P) (⟨r, hr⟩ : P.primeCompl)).map g

end GlobalTheory.LocM.Lift
