import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.VFEqEmultiplicity

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

/- English proof (translation)
Rewrite using `[FractionalIdeal.count_coe K v hI, Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot, HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI v]`.
-/
theorem count_coe_eq_multiplicity {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors R) K) = (multiplicity v.asIdeal I : ℤ) := by
  rw [FractionalIdeal.count_coe K v hI, Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI v]

/- English proof (translation)
Rewrite using `[← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]`. Repeatedly rewrite using `[h]`.
-/
theorem eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {I J : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  simp_rw [h]

def belowP {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (P : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))
  isPrime := P.isPrime.comap _
  ne_bot := by
    intro h
    have hmax : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
    exact Ring.ne_bot_of_isMaximal_of_not_isField hmax (NumberField.RingOfIntegers.not_isField F) h

/- English proof (translation)
Establish `hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ v.asIdeal`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]`. Conclude with `bot_le`. Use `haveI := v.isMaximal`. Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker`.

Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises. Rewrite using `[← hQc, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]`. Use `⟨⟨Q, hQ.isPrime, hQ0⟩, ?_⟩` and prove the remaining obligations.

Use `ext1`. Conclude with `hQc`.
-/
theorem exists_above {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ P : HeightOneSpectrum (𝓞 K), belowP P = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact bot_le
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQc, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, ?_⟩
  ext1
  exact hQc

/- English proof (translation)
Introduce `K F _ _ _ _ _ h2 J w hJ0 hc`. Use `set wv : HeightOneSpectrum (𝓞 F) → ℕ := fun v => w v.asIdeal with hwv`. Establish `hcJ : ∀ P : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K P J = ((P.asIdeal.ramificationIdx (𝓞 F) * wv (belowP P) : ℕ) : ℤ)` using `fun P => hc _ P (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal) rfl`. Establish `he : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.ramificationIdx (𝓞 F) ≠ 0`. Introduce `P`.

Use `haveI := P.isPrime`. Conclude with `(Ideal.ramificationIdx_pos P.asIdeal (𝓞 F)).ne'`. Establish `hfinJ` using `FractionalIdeal.finite_factors (K := K) J`. Establish `hsupp : {v : HeightOneSpectrum (𝓞 F) | wv v ≠ 0}.Finite`. Use `(hfinJ.image belowP).subset ?_` and prove the remaining obligations.

Introduce `v hv`. Take `⟨P, rfl⟩` from `exists_above (K := K) v`. Use `⟨P, ?_, rfl⟩` and prove the remaining obligations. Use `show FractionalIdeal.count K P J ≠ 0`. Rewrite using `[hcJ P]`.

Conclude with `Nat.mul_ne_zero (he P) hv` after adjusting the coercions. Establish `hmsF : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ wv v`. Use `hsupp.subset ?_` and prove the remaining obligations. Introduce `v hv h0`. Apply `hv` to reduce the goal to its premises.

Use `show v.asIdeal ^ wv v = 1`. Rewrite using `[show wv v = 0 from h0, pow_zero]`. Use `set IF : Ideal (𝓞 F) := ∏ᶠ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ wv v with hIF`. Establish `hIF0 : IF ≠ ⊥`. Rewrite using `[hIF, finprod_eq_prod _ hmsF]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot`. Establish `hcF : ∀ v : HeightOneSpectrum (𝓞 F), multiplicity v.asIdeal IF = wv v`. Introduce `v`. Establish `h1` using `count_coe_eq_multiplicity (K := F) v hIF0`. Establish `h2 : ((IF : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = ∏ᶠ u : HeightOneSpectrum (𝓞 F), (u.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ ((wv u : ℕ) : ℤ)`.

Rewrite using `[hIF, FractionalIdeal.coeIdeal_finprod (nonZeroDivisors (𝓞 F)) F le_rfl]`. Repeatedly rewrite using `[FractionalIdeal.coeIdeal_pow, zpow_natCast]`. Rewrite `h1` using `[h2, FractionalIdeal.count_finprod]`. Conclude with `h1.symm` after adjusting the coercions. Use `show {u | ¬ ((wv u : ℕ) : ℤ) = 0}.Finite`.

Simplify using `using hsupp`. Establish `hJ : J = ((IF.map (algebraMap (𝓞 F) (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)`. Establish `hm0 : IF.map (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥` using `Ideal.map_ne_bot_of_ne_bot hIF0`. Use `eq_of_count_eq hJ0 (by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]) fun P => ?_` and prove the remaining obligations. Rewrite using `[hcJ P, count_coe_eq_multiplicity P hm0]`.

Use `haveI : P.asIdeal.LiesOver (belowP (K := K) (F := F) P).asIdeal := ⟨rfl⟩`. Establish `hem` using `Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hIF0 (belowP (K := K) (F := F) P).irreducible P.irreducible P.ne_bot`. Rewrite `hem` using `[(FiniteMultiplicity.of_prime_left P.prime hm0).emultiplicity_eq_multiplicity, (FiniteMultiplicity.of_prime_left (belowP (K := K) (F := F) P).prime hIF0).emultiplicity_eq_multiplicity, hcF, Ideal.ramificationIdx'_eq_ramificationIdx _ P.asIdeal (belowP (K := K) (F := F) P).ne_bot]`. Conclude with `hem.symm` after adjusting the coercions. Establish `hfr : Module.finrank (𝓞 F) (𝓞 K) = 2`.

Rewrite using `[← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K]`. Conclude with `h2`. Establish `hNJ : (FractionalIdeal.absNorm J : ℝ) = ((Ideal.absNorm IF : ℕ) : ℝ) ^ 2`. Rewrite using `[hJ, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_algebraMap, hfr]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hNIF : Ideal.absNorm IF = ∏ᶠ v : HeightOneSpectrum (𝓞 F), Ideal.absNorm v.asIdeal ^ wv v`. Rewrite using `[hIF, map_finprod Ideal.absNorm hmsF]`. Simplify using `only [map_pow]`. Establish `hms2 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal ^ wv v`.

Use `hsupp.subset ?_` and prove the remaining obligations. Introduce `v hv h0`. Apply `hv` to reduce the goal to its premises. Use `show Ideal.absNorm v.asIdeal ^ wv v = 1`. Rewrite using `[show wv v = 0 from h0, pow_zero]`.

Establish `hms3 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v`. Use `hsupp.subset ?_` and prove the remaining obligations. Introduce `v hv h0`. Apply `hv` to reduce the goal to its premises. Use `show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v = 1`.

Rewrite using `[show wv v = 0 from h0, pow_zero]`. Set `e : HeightOneSpectrum (𝓞 F) ≃ {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}` to `{ toFun := fun v => ⟨v.asIdeal, v.isMaximal⟩ invFun := fun p => ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (NumberField.RingOfIntegers.not_isField F)⟩ left_inv := fun v => rfl right_inv := fun p => rfl }`. Establish `ht : (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ w 𝔭.1) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v`. Rewrite using `[← e.tprod_eq]`. Conclude with `tprod_eq_finprod hms3`.

Establish `hcast` using `map_finprod (Nat.castRingHom ℝ) hms2`. Simplify using `only [map_pow, eq_natCast] at hcast`. Rewrite using `[hNJ, hNIF, ht, hcast]`.
-/
theorem norm_mass_assembly : NormAssembly := by
  intro K F _ _ _ _ _ h2 J w hJ0 hc
  classical
  set wv : HeightOneSpectrum (𝓞 F) → ℕ := fun v => w v.asIdeal with hwv

  have hcJ : ∀ P : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K P J =
      ((P.asIdeal.ramificationIdx (𝓞 F) * wv (belowP P) : ℕ) : ℤ) := fun P =>
    hc _ P (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal) rfl
  have he : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := by
    intro P
    haveI := P.isPrime
    exact (Ideal.ramificationIdx_pos P.asIdeal (𝓞 F)).ne'

  have hfinJ := FractionalIdeal.finite_factors (K := K) J
  have hsupp : {v : HeightOneSpectrum (𝓞 F) | wv v ≠ 0}.Finite := by
    refine (hfinJ.image belowP).subset ?_
    intro v hv
    obtain ⟨P, rfl⟩ := exists_above (K := K) v
    refine ⟨P, ?_, rfl⟩
    show FractionalIdeal.count K P J ≠ 0
    rw [hcJ P]
    exact_mod_cast Nat.mul_ne_zero (he P) hv

  have hmsF : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show v.asIdeal ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  set IF : Ideal (𝓞 F) := ∏ᶠ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ wv v with hIF
  have hIF0 : IF ≠ ⊥ := by
    rw [hIF, finprod_eq_prod _ hmsF]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  have hcF : ∀ v : HeightOneSpectrum (𝓞 F), multiplicity v.asIdeal IF = wv v := by
    intro v
    have h1 := count_coe_eq_multiplicity (K := F) v hIF0
    have h2 : ((IF : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ᶠ u : HeightOneSpectrum (𝓞 F), (u.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ ((wv u : ℕ) : ℤ) := by
      rw [hIF, FractionalIdeal.coeIdeal_finprod (nonZeroDivisors (𝓞 F)) F le_rfl]
      simp_rw [FractionalIdeal.coeIdeal_pow, zpow_natCast]
    rw [h2, FractionalIdeal.count_finprod] at h1
    · exact_mod_cast h1.symm
    · show {u | ¬ ((wv u : ℕ) : ℤ) = 0}.Finite
      simpa using hsupp

  have hJ : J = ((IF.map (algebraMap (𝓞 F) (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have hm0 : IF.map (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hIF0
    refine eq_of_count_eq hJ0 (by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]) fun P => ?_
    rw [hcJ P, count_coe_eq_multiplicity P hm0]
    haveI : P.asIdeal.LiesOver (belowP (K := K) (F := F) P).asIdeal := ⟨rfl⟩
    have hem := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hIF0
      (belowP (K := K) (F := F) P).irreducible P.irreducible P.ne_bot
    rw [(FiniteMultiplicity.of_prime_left P.prime hm0).emultiplicity_eq_multiplicity,
      (FiniteMultiplicity.of_prime_left (belowP (K := K) (F := F) P).prime hIF0).emultiplicity_eq_multiplicity,
      hcF, Ideal.ramificationIdx'_eq_ramificationIdx _ P.asIdeal (belowP (K := K) (F := F) P).ne_bot] at hem
    exact_mod_cast hem.symm

  have hfr : Module.finrank (𝓞 F) (𝓞 K) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K]
    exact h2
  have hNJ : (FractionalIdeal.absNorm J : ℝ) = ((Ideal.absNorm IF : ℕ) : ℝ) ^ 2 := by
    rw [hJ, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_algebraMap, hfr]
    push_cast
    rfl
  have hNIF : Ideal.absNorm IF = ∏ᶠ v : HeightOneSpectrum (𝓞 F), Ideal.absNorm v.asIdeal ^ wv v := by
    rw [hIF, map_finprod Ideal.absNorm hmsF]
    simp only [map_pow]
  have hms2 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show Ideal.absNorm v.asIdeal ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  have hms3 : Function.HasFiniteMulSupport
      fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  let e : HeightOneSpectrum (𝓞 F) ≃ {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    { toFun := fun v => ⟨v.asIdeal, v.isMaximal⟩
      invFun := fun p => ⟨p.1, p.2.isPrime,
        Ring.ne_bot_of_isMaximal_of_not_isField p.2 (NumberField.RingOfIntegers.not_isField F)⟩
      left_inv := fun v => rfl
      right_inv := fun p => rfl }
  have ht : (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ w 𝔭.1) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v := by
    rw [← e.tprod_eq]
    exact tprod_eq_finprod hms3
  have hcast := map_finprod (Nat.castRingHom ℝ) hms2
  simp only [map_pow, eq_natCast] at hcast
  rw [hNJ, hNIF, ht, hcast]

end PI.UnitaryGroupMassFormula.CntFormula.R6
