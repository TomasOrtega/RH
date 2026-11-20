import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Establish `hpr : Prime (r : 𝓞 ℚ)`. Establish `h1 : Prime ((Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) (r : 𝓞 ℚ))`. Rewrite using `[map_natCast]`. Conclude with `Nat.prime_iff_prime_int.mp hr`. Conclude with `(MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toMulEquiv).mp h1`.

Establish `hne : (r : 𝓞 ℚ) ≠ 0` using `hpr.ne_zero`. Establish `hspan : v.asIdeal = Ideal.span {(r : 𝓞 ℚ)}`. Establish `hP : (Ideal.span {(r : 𝓞 ℚ)}).IsPrime` using `(Ideal.span_singleton_prime hne).mpr hpr`. Establish `hbot : Ideal.span {(r : 𝓞 ℚ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `hne`. Establish `hmax` using `hP.isMaximal hbot`. Establish `hle : Ideal.span {(r : 𝓞 ℚ)} ≤ v.asIdeal`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hv`.

Conclude with `(hmax.eq_of_le v.isPrime.ne_top hle).symm`. Establish `hint : v.intValuation (r : 𝓞 ℚ) = WithZero.exp (-1 : ℤ)` using `v.intValuation_singleton hne hspan`. Establish `hval : ((v.valuationOfNeZero a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ)`. Rewrite using `[HeightOneSpectrum.valuationOfNeZero_eq, ha, ← hint]`. Establish `: ((r : ℚ)) = algebraMap (𝓞 ℚ) ℚ (r : 𝓞 ℚ)` using `by simp`.

Rewrite using `[this, HeightOneSpectrum.valuation_of_algebraMap]`. Establish `h2 : v.valuationOfNeZero a = Multiplicative.ofAdd (-1 : ℤ)`. Apply `WithZero.coe_injective` to reduce the goal to its premises. Rewrite using `[hval]`. Both sides reduce to the same expression.

Unfold `UpperTheory.V.Kum.ordv`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.
-/
private theorem ordv_prime (r : ℕ) (hr : r.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal)
    (a : ℚˣ) (ha : (a : ℚ) = r) : UpperTheory.V.Kum.ordv v a = 1 := by
  have hpr : Prime (r : 𝓞 ℚ) := by
    have h1 : Prime ((Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) (r : 𝓞 ℚ)) := by
      rw [map_natCast]
      exact Nat.prime_iff_prime_int.mp hr
    exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toMulEquiv).mp h1
  have hne : (r : 𝓞 ℚ) ≠ 0 := hpr.ne_zero
  have hspan : v.asIdeal = Ideal.span {(r : 𝓞 ℚ)} := by
    have hP : (Ideal.span {(r : 𝓞 ℚ)}).IsPrime := (Ideal.span_singleton_prime hne).mpr hpr
    have hbot : Ideal.span {(r : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hne
    have hmax := hP.isMaximal hbot
    have hle : Ideal.span {(r : 𝓞 ℚ)} ≤ v.asIdeal := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hv
    exact (hmax.eq_of_le v.isPrime.ne_top hle).symm
  have hint : v.intValuation (r : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := v.intValuation_singleton hne hspan
  have hval : ((v.valuationOfNeZero a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, ha, ← hint]
    have : ((r : ℚ)) = algebraMap (𝓞 ℚ) ℚ (r : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
  have h2 : v.valuationOfNeZero a = Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [hval]
    rfl
  unfold UpperTheory.V.Kum.ordv
  rw [h2]
  simp

/- English proof (translation)
Introduce `Ω _ _ _ r M hr hM A hA ρ ζ hρ hζ`. Establish `pb` using `placeBasic Ω`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `hr0 : (r : Ω) ≠ 0` using `by exact_mod_cast hr.ne_zero`. Establish `hM0 : M ≠ 0`.

Introduce and unpack `rfl`. Simplify using `[Nat.coprime_zero_left] at hM`. Conclude with `hr.ne_one hM`. Use `haveI : NeZero M := ⟨hM0⟩`. Establish `hρ0 : ρ ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hρ` using `[zero_pow hM0]`. Conclude with `hr0 hρ.symm`. Establish `hnot : ¬ Over A M` using `fun h => pb.2.2.2.1 A M r hM h hA`. Establish `hfix : Ine (F` using `ℚ) A ≤ fixMu ℚ Ω M := pb.2.2.2.2.1 A M hnot`.

Establish `hroot : ∀ g : G ℚ Ω, (g ρ / ρ) ^ M = 1`. Introduce `g`. Rewrite using `[div_pow, ← map_pow, hρ, map_natCast, div_self hr0]`. Establish `hgne : ∀ g : G ℚ Ω, g ρ / ρ ≠ 0` using `fun g => div_ne_zero (by simpa using hρ0) hρ0`. Set `χ : ↥(Ine (F` to `ℚ) A) →* Ωˣ := { toFun := fun g => Units.mk0 ((g : G ℚ Ω) ρ / ρ) (hgne g) map_one' := by`.

Use `ext`. Simplify using `[div_self hρ0]`. Use the proof step `map_mul' := by`. Introduce `g h`. Use `ext`.

Establish `hc : (g : G ℚ Ω) ((h : G ℚ Ω) ρ / ρ) = (h : G ℚ Ω) ρ / ρ` using `hfix g.2 _ (hroot h)`. Establish `hh : (h : G ℚ Ω) ρ = ((h : G ℚ Ω) ρ / ρ) * ρ`. Clear the denominators using the available nonvanishing facts. Simplify using `only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, AlgEquiv.mul_apply]`. Rewrite using `[hh, map_mul, hc]`.

Clear denominators, using `}` for the nonvanishing conditions. Establish `hχ : ∀ g, ((χ g : Ωˣ) : Ω) = (g : G ℚ Ω) ρ / ρ` using `fun g => rfl`. Establish `hle : χ.range ≤ rootsOfUnity M Ω`. Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[mem_rootsOfUnity]`.

Use `ext`. Rewrite using `[Units.val_pow_eq_pow_val, hχ, hroot, Units.val_one]`. Use `haveI : Finite χ.range := Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)`. Establish `hd0 : 0 < Nat.card χ.range` using `Nat.card_pos`. Establish `hfixd : ∀ g ∈ Ine (F` using `ℚ) A, g (ρ ^ Nat.card χ.range) = ρ ^ Nat.card χ.range := by`.

Introduce `g hg`. Establish `h1` using `congrArg (fun x : χ.range => ((x : Ωˣ) : Ω)) (pow_card_eq_one' (x := (⟨χ ⟨g, hg⟩, ⟨_, rfl⟩⟩ : χ.range)))`. Simplify using `only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hχ, OneMemClass.coe_one, Units.val_one] at h1`. Rewrite `h1` using `[div_pow, div_eq_one_iff_eq (pow_ne_zero _ hρ0)]`. Rewrite using `[map_pow]`.

Conclude with `h1`. Take `⟨v, hvA, -, hvr⟩` from `pb.2.2.2.2.2.2.2.2.1 A r hr hA`. Set `a : ℚˣ` to `Units.mk0 (r : ℚ) (by exact_mod_cast hr.ne_zero)`. Establish `ha1 : UpperTheory.V.Kum.ordv v a = 1` using `ordv_prime r hr v hvr a rfl`. Establish `hpow : UpperTheory.V.Kum.ordv v (a ^ Nat.card χ.range) = Nat.card χ.range`.

Unfold `UpperTheory.V.Kum.ordv at ha1 ⊢`. Rewrite using `[map_pow, toAdd_pow, nsmul_eq_mul, ← mul_neg, ha1, mul_one]`. Establish `hdv` using `UpperTheory.V.Kum.dvdOfIne ℚ Ω M A v (ρ ^ Nat.card χ.range) (a ^ Nat.card χ.range) hvA (by`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hρ]`. Simplify using `[a]) hfixd`.

Rewrite `hdv` using `[hpow]`. Establish `hMd : M ∣ Nat.card χ.range` using `by exact_mod_cast hdv`. Establish `hMle : M ≤ Nat.card χ.range` using `Nat.le_of_dvd hd0 hMd`. Establish `hcard : Nat.card χ.range ≤ Nat.card (rootsOfUnity M Ω)` using `Subgroup.card_le_of_le hle`. Establish `heq : χ.range = rootsOfUnity M Ω` using `Subgroup.eq_of_le_of_card_ge hle (le_trans (card_rootsOfUnity Ω M) hMle)`.

Establish `hζ0 : ζ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hζ` using `[zero_pow hM0]`. Conclude with `zero_ne_one hζ`. Establish `hu : Units.mk0 ζ hζ0 ∈ rootsOfUnity M Ω`.

Rewrite using `[mem_rootsOfUnity]`. Use `ext`. Simplify using `[hζ]`. Rewrite `hu` using `[← heq]`. Take `⟨g, hg⟩` from `hu`.

Use `⟨g, g.2, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg Units.val hg`. Rewrite `h2` using `[hχ, Units.val_mk0, div_eq_iff hρ0]`. Conclude with `h2`.
-/
theorem UpperTheory.V.ML.ineRad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (r M : ℕ), r.Prime → M.Coprime r → ∀ A : ValuationSubring Ω, Over A r → ∀ ρ ζ : Ω, ρ ^ M = (r : Ω) → ζ ^ M = 1 → ∃ t ∈ Ine (F := ℚ) A, t ρ = ζ * ρ := by
  intro Ω _ _ _ r M hr hM A hA ρ ζ hρ hζ
  have pb := placeBasic Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hr0 : (r : Ω) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp [Nat.coprime_zero_left] at hM
    exact hr.ne_one hM
  haveI : NeZero M := ⟨hM0⟩
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hρ
    exact hr0 hρ.symm
  have hnot : ¬ Over A M := fun h => pb.2.2.2.1 A M r hM h hA
  have hfix : Ine (F := ℚ) A ≤ fixMu ℚ Ω M := pb.2.2.2.2.1 A M hnot
  have hroot : ∀ g : G ℚ Ω, (g ρ / ρ) ^ M = 1 := by
    intro g
    rw [div_pow, ← map_pow, hρ, map_natCast, div_self hr0]
  have hgne : ∀ g : G ℚ Ω, g ρ / ρ ≠ 0 := fun g =>
    div_ne_zero (by simpa using hρ0) hρ0
  let χ : ↥(Ine (F := ℚ) A) →* Ωˣ :=
    { toFun := fun g => Units.mk0 ((g : G ℚ Ω) ρ / ρ) (hgne g)
      map_one' := by
        ext
        simp [div_self hρ0]
      map_mul' := by
        intro g h
        ext
        have hc : (g : G ℚ Ω) ((h : G ℚ Ω) ρ / ρ) = (h : G ℚ Ω) ρ / ρ :=
          hfix g.2 _ (hroot h)
        have hh : (h : G ℚ Ω) ρ = ((h : G ℚ Ω) ρ / ρ) * ρ := by
          field_simp
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, AlgEquiv.mul_apply]
        rw [hh, map_mul, hc]
        field_simp }
  have hχ : ∀ g, ((χ g : Ωˣ) : Ω) = (g : G ℚ Ω) ρ / ρ := fun g => rfl
  have hle : χ.range ≤ rootsOfUnity M Ω := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, hχ, hroot, Units.val_one]
  haveI : Finite χ.range :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hd0 : 0 < Nat.card χ.range := Nat.card_pos
  have hfixd : ∀ g ∈ Ine (F := ℚ) A, g (ρ ^ Nat.card χ.range) = ρ ^ Nat.card χ.range := by
    intro g hg
    have h1 := congrArg (fun x : χ.range => ((x : Ωˣ) : Ω))
      (pow_card_eq_one' (x := (⟨χ ⟨g, hg⟩, ⟨_, rfl⟩⟩ : χ.range)))
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hχ, OneMemClass.coe_one,
      Units.val_one] at h1
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hρ0)] at h1
    rw [map_pow]
    exact h1
  obtain ⟨v, hvA, -, hvr⟩ := pb.2.2.2.2.2.2.2.2.1 A r hr hA
  let a : ℚˣ := Units.mk0 (r : ℚ) (by exact_mod_cast hr.ne_zero)
  have ha1 : UpperTheory.V.Kum.ordv v a = 1 := ordv_prime r hr v hvr a rfl
  have hpow : UpperTheory.V.Kum.ordv v (a ^ Nat.card χ.range) = Nat.card χ.range := by
    unfold UpperTheory.V.Kum.ordv at ha1 ⊢
    rw [map_pow, toAdd_pow, nsmul_eq_mul, ← mul_neg, ha1, mul_one]
  have hdv := UpperTheory.V.Kum.dvdOfIne ℚ Ω M A v (ρ ^ Nat.card χ.range) (a ^ Nat.card χ.range) hvA
    (by
      rw [← pow_mul, mul_comm, pow_mul, hρ]
      simp [a]) hfixd
  rw [hpow] at hdv
  have hMd : M ∣ Nat.card χ.range := by exact_mod_cast hdv
  have hMle : M ≤ Nat.card χ.range := Nat.le_of_dvd hd0 hMd
  have hcard : Nat.card χ.range ≤ Nat.card (rootsOfUnity M Ω) := Subgroup.card_le_of_le hle
  have heq : χ.range = rootsOfUnity M Ω :=
    Subgroup.eq_of_le_of_card_ge hle (le_trans (card_rootsOfUnity Ω M) hMle)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hζ
    exact zero_ne_one hζ
  have hu : Units.mk0 ζ hζ0 ∈ rootsOfUnity M Ω := by
    rw [mem_rootsOfUnity]
    ext
    simp [hζ]
  rw [← heq] at hu
  obtain ⟨g, hg⟩ := hu
  refine ⟨g, g.2, ?_⟩
  have h2 := congrArg Units.val hg
  rw [hχ, Units.val_mk0, div_eq_iff hρ0] at h2
  exact h2
