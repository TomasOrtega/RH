import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeDvdSubOneCyclotomicIrreducibleOverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicCrossingFieldDecidingFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobRestrictScalarsOfPrimeAbsNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeAbsNormEqOfIrreducibleCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtensionStatement

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Published

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ L _ _ g S hS`. Establish `: IsGalois F Ω` using `{}`. Take `⟨g', rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) Ω g`. Establish `: NumberField L` using `NumberField.of_module_finite F L`. Take `⟨m, hm, hdvd, hirr⟩` from `GlobalTheory.T.exists_prime_dvd_sub_one_cyclotomic_irreducible_over L (Module.finrank F L) Module.finrank_pos.ne'`.

Take `⟨Z, τ, hZ, hZirr, hcross⟩` from `GlobalTheory.T.exists_cyclotomic_crossing_field_deciding_frobenius F Ω L g' m hm hdvd hirr`. Establish `: NumberField Z` using `NumberField.of_module_finite F Z`. Establish `: IsAlgClosure Z Ω` using `⟨IsAlgClosure.isAlgClosed F, inferInstance⟩`. Establish `hfin` using `hS.union (GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension F Ω L)`. Set `u : HeightOneSpectrum (𝓞 Z) → HeightOneSpectrum (𝓞 F)` to `fun w => w.under (𝓞 F)`.

Establish `hu : ∀ w : HeightOneSpectrum (𝓞 Z), w.asIdeal.LiesOver (u w).asIdeal` using `fun w => ⟨rfl⟩`. Establish `hfin' : (u ⁻¹' (S ∪ {v | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ ¬ Ine (F` using `F) B ≤ L.fixingSubgroup})).Finite := by`. Use `hfin.preimage' fun v _ => ?_` and prove the remaining obligations. Use `v.isMaximal` as an intermediate fact. Use `((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 Z)).preimage (f := fun w : HeightOneSpectrum (𝓞 Z) => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_` and prove the remaining obligations.

Introduce and unpack `w rfl`. Conclude with `⟨w.isPrime, hu w⟩`. Take `⟨w, hw, hp, hτ⟩` from `GlobalTheory.T.exists_prime_absNorm_eq_of_irreducible_cyclotomic' Z m hm hZirr τ _ hfin'`. Take `⟨B, hB⟩` from `exists_isPlaceOver Ω w`. Take `⟨σ, hσ⟩` from `exists_isFrob hB`.

Take `⟨hN, hBv, hσv⟩` from `GlobalTheory.T.isFrob_restrictScalars_of_prime_absNorm' F Ω Z w (u w) (hu w) hp B hB σ hσ`. Simplify using `only [Set.mem_preimage, Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_and, not_not] at hw`. Use `⟨u w, hw.1, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 _).1 (hN ▸ hp), B, hBv, hw.2 B hBv, σ.restrictScalars F, hσv, ?_⟩` and prove the remaining obligations. Establish `hmw : ((m : ℕ) : 𝓞 Z) ∉ w.asIdeal`. Introduce `h`.

Establish `: Fact m.Prime` using `⟨hm⟩`. Establish `h1 : Ideal.absNorm w.asIdeal ∣ m ^ Module.finrank ℤ (𝓞 Z)`. Rewrite using `[← Ideal.absNorm_span_natCast]`. Conclude with `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)`. Establish `h2` using `(Nat.prime_dvd_prime_iff_eq hp hm).1 (hp.dvd_of_dvd_pow h1)`.

Rewrite `hτ` using `[h2, ZMod.natCast_self]`. Conclude with `τ.ne_zero hτ.symm`. Establish `key` using `hcross (σ.restrictScalars F) (fun x => σ.commutes x) fun ζ hζ => by`. Establish `hq : ζ ^ (τ : ZMod m).val = ζ ^ normV w`. Rewrite using `[← hτ, ZMod.val_natCast]`.

Conclude with `(pow_eq_pow_mod _ hζ).symm`. Rewrite using `[hq]`. Establish `h1` using `not_valuation_lt_one_of_isPlaceOver hmw hB 1`. Rewrite `h1` using `[pow_one]`. Use `eq_of_pow_eq_one B h1 ?_ ?_ (hσ.2 ζ (valuation_eq_one_of_pow_eq_one B hm.ne_zero hζ).le)` and prove the remaining obligations.

Rewrite using `[← map_pow, hζ, map_one]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ, one_pow]`. Rewrite `key` using `[← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]`. Then use the resulting hypothesis.
-/
theorem chebotarevDegreeOne' : ChebotarevDegreeOne := by
  intro F Ω _ _ _ _ _ L _ _ g S hS
  have : IsGalois F Ω := {}
  obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) Ω g
  have : NumberField L := NumberField.of_module_finite F L
  obtain ⟨m, hm, hdvd, hirr⟩ := GlobalTheory.T.exists_prime_dvd_sub_one_cyclotomic_irreducible_over L (Module.finrank F L) Module.finrank_pos.ne'
  obtain ⟨Z, τ, hZ, hZirr, hcross⟩ := GlobalTheory.T.exists_cyclotomic_crossing_field_deciding_frobenius F Ω L g' m hm hdvd hirr
  have : NumberField Z := NumberField.of_module_finite F Z
  have : IsAlgClosure Z Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  have hfin := hS.union (GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension F Ω L)
  let u : HeightOneSpectrum (𝓞 Z) → HeightOneSpectrum (𝓞 F) := fun w => w.under (𝓞 F)
  have hu : ∀ w : HeightOneSpectrum (𝓞 Z), w.asIdeal.LiesOver (u w).asIdeal := fun w => ⟨rfl⟩
  have hfin' : (u ⁻¹' (S ∪ {v | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ¬ Ine (F := F) B ≤ L.fixingSubgroup})).Finite := by
    refine hfin.preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 Z)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 Z) => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, hu w⟩
  obtain ⟨w, hw, hp, hτ⟩ := GlobalTheory.T.exists_prime_absNorm_eq_of_irreducible_cyclotomic' Z m hm hZirr τ _ hfin'
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hB
  obtain ⟨hN, hBv, hσv⟩ := GlobalTheory.T.isFrob_restrictScalars_of_prime_absNorm' F Ω Z w (u w) (hu w) hp B hB σ hσ
  simp only [Set.mem_preimage, Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_and, not_not] at hw
  refine ⟨u w, hw.1, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 _).1 (hN ▸ hp),
    B, hBv, hw.2 B hBv, σ.restrictScalars F, hσv, ?_⟩
  have hmw : ((m : ℕ) : 𝓞 Z) ∉ w.asIdeal := by
    intro h
    have : Fact m.Prime := ⟨hm⟩
    have h1 : Ideal.absNorm w.asIdeal ∣ m ^ Module.finrank ℤ (𝓞 Z) := by
      rw [← Ideal.absNorm_span_natCast]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
    have h2 := (Nat.prime_dvd_prime_iff_eq hp hm).1 (hp.dvd_of_dvd_pow h1)
    rw [h2, ZMod.natCast_self] at hτ
    exact τ.ne_zero hτ.symm
  have key := hcross (σ.restrictScalars F) (fun x => σ.commutes x) fun ζ hζ => by
    have hq : ζ ^ (τ : ZMod m).val = ζ ^ normV w := by
      rw [← hτ, ZMod.val_natCast]
      exact (pow_eq_pow_mod _ hζ).symm
    rw [hq]
    have h1 := not_valuation_lt_one_of_isPlaceOver hmw hB 1
    rw [pow_one] at h1
    refine eq_of_pow_eq_one B h1 ?_ ?_ (hσ.2 ζ (valuation_eq_one_of_pow_eq_one B hm.ne_zero hζ).le)
    · rw [← map_pow, hζ, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  rwa [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv,
    mul_inv_eq_one] at key

/- English proof (translation)
The claim follows from `chebotarevDegreeOne_iff_cheb.1 chebotarevDegreeOne'`.
-/
theorem cheb_holds : GlobalTheory.TwSys.Cheb :=
  chebotarevDegreeOne_iff_cheb.1 chebotarevDegreeOne'

end GlobalTheory.Published

end
