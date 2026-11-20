import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightSpaceFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KStableHighestWeightVector
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Introduce `S R _ _ _ _ _ hR hS`. Use `haveI : IsNoetherianRing S := hS.1`. Use `haveI : IsNoetherianRing R := hR.noeth`. Use `haveI : Module.Flat S R := (c3a (maximalIdeal S) hR).1`. Establish `hdim : ringKrullDim R = ringKrullDim S`.

Establish `h` using `(c3c (maximalIdeal S) hR).1 ⊥`. Rewrite `h` using `[Ideal.map_bot]`. Unfold `dimAt at h`. Rewrite `h` using `[Ideal.map_bot]`. Establish `hu : (maximalIdeal S).primeCompl ≤ IsUnit.submonoid S` using `fun x hx => IsLocalRing.notMem_maximalIdeal.mp hx`.

Establish `e : S ≃+* Localization.AtPrime (maximalIdeal S)` using `(IsLocalization.atUnits S (maximalIdeal S).primeCompl hu).toRingEquiv`. Rewrite using `[← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R), h, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_eq_of_ringEquiv e.symm]`. Establish `hcomap : Ideal.comap (algebraMap S R) (maximalIdeal R) = maximalIdeal S`. Simplify using `using hR.comap_pow 1`. Establish `hRCM : IsCM R`.

Take `⟨-, n, hn, rs, hlen, hmem, hreg⟩` from `hS`. Establish `hmem' : ∀ r ∈ rs.map (algebraMap S R), r ∈ maximalIdeal R`. Introduce `r hr`. Take `⟨a, ha, rfl⟩` from `List.mem_map.mp hr`. Establish `: a ∈ Ideal.comap (algebraMap S R) (maximalIdeal R)`.

Rewrite using `[hcomap]`. Conclude with `hmem a ha`. Conclude with `this`. Use `⟨inferInstance, n, hdim.trans hn, rs.map (algebraMap S R), by simp [hlen], hmem', ?_⟩` and prove the remaining obligations. Conclude with `(IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem').mpr hreg.toIsWeaklyRegular.of_flat`.

Conclude with `⟨hRCM, fun p _ => hRCM.height_add_ringKrullDim_quotient p, fun p _ => hS.height_add_ringKrullDim_quotient p, hdim⟩`.
-/
theorem UpperTheory.V.CA.cpl_cm :
    ∀ (S R : Type) [CommRing S] [IsLocalRing S] [CommRing R] [IsLocalRing R] [Algebra S R], IsCplAt (maximalIdeal S) R → IsCM S → IsCM R ∧ DimFormula R ∧ DimFormula S ∧ ringKrullDim R = ringKrullDim S := by
  intro S R _ _ _ _ _ hR hS
  haveI : IsNoetherianRing S := hS.1
  haveI : IsNoetherianRing R := hR.noeth
  haveI : Module.Flat S R := (c3a (maximalIdeal S) hR).1
  have hdim : ringKrullDim R = ringKrullDim S := by
    have h := (c3c (maximalIdeal S) hR).1 ⊥
    rw [Ideal.map_bot] at h
    unfold dimAt at h
    rw [Ideal.map_bot] at h
    have hu : (maximalIdeal S).primeCompl ≤ IsUnit.submonoid S := fun x hx =>
      IsLocalRing.notMem_maximalIdeal.mp hx
    have e : S ≃+* Localization.AtPrime (maximalIdeal S) :=
      (IsLocalization.atUnits S (maximalIdeal S).primeCompl hu).toRingEquiv
    rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R), h,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_eq_of_ringEquiv e.symm]
  have hcomap : Ideal.comap (algebraMap S R) (maximalIdeal R) = maximalIdeal S := by
    simpa using hR.comap_pow 1
  have hRCM : IsCM R := by
    obtain ⟨-, n, hn, rs, hlen, hmem, hreg⟩ := hS
    have hmem' : ∀ r ∈ rs.map (algebraMap S R), r ∈ maximalIdeal R := by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      have : a ∈ Ideal.comap (algebraMap S R) (maximalIdeal R) := by
        rw [hcomap]
        exact hmem a ha
      exact this
    refine ⟨inferInstance, n, hdim.trans hn, rs.map (algebraMap S R), by simp [hlen], hmem', ?_⟩
    exact (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem').mpr
      hreg.toIsWeaklyRegular.of_flat
  exact ⟨hRCM, fun p _ => hRCM.height_add_ringKrullDim_quotient p,
    fun p _ => hS.height_add_ringKrullDim_quotient p, hdim⟩
