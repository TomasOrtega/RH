import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.BauerFixIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.RayPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.SplitCyc

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn hmem`. Distinguish the cases in `h1 : n = 1`.

Substitute `h1` using the available equality. Conclude with `absurd ((Ideal.eq_top_iff_one I).mpr (by simpa using hmem)) hI.ne_top`. Establish `hp` using `Nat.minFac_prime h1`. Take `⟨m, hm⟩` from `Nat.minFac_dvd n`. Rewrite `hmem` using `[hm, Nat.cast_mul]`.

Break down `hI.mem_or_mem hmem with h | h` into its components or cases. Conclude with `⟨_, hp, h⟩`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Rewrite `hm` using `[mul_zero]`.

Conclude with `hn hm`. Establish `hlt : m < n` using `by conv_rhs => rw [hm]`. Conclude with `lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt`. Conclude with `ih m hlt hm0 h`.
-/
private theorem exists_prime_mem_of_mem {R : Type} [CommRing R] (I : Ideal R) (hI : I.IsPrime) :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ I → ∃ p : ℕ, p.Prime ∧ (p : R) ∈ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one I).mpr (by simpa using hmem)) hI.ne_top
    · have hp := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      rw [hm, Nat.cast_mul] at hmem
      rcases hI.mem_or_mem hmem with h | h
      · exact ⟨_, hp, h⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm
          exact hn hm
        have hlt : m < n := by
          conv_rhs => rw [hm]
          exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt
        exact ih m hlt hm0 h

/- English proof (translation)
Express the relevant statement in the definitionally equal form `IsCyclotomicExtension {n} K (IntermediateField.adjoin K {ζ}).toSubalgebra`. Establish `hi : IsIntegral K ζ`. Use `⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), ?_⟩` and prove the remaining obligations. Simplify using `[hζ.pow_eq_one]`. Rewrite using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic]`.

Conclude with `hζ.adjoin_isCyclotomicExtension K`.
-/
private theorem cyc_adjoin (K : Type) {L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n] {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} K K⟮ζ⟯ := by
  change IsCyclotomicExtension {n} K (IntermediateField.adjoin K {ζ}).toSubalgebra
  have hi : IsIntegral K ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), ?_⟩
    simp [hζ.pow_eq_one]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension K

/- English proof (translation)
Introduce `Ω _ _ _ 𝔪 ζ hζ`. Use `set N := Ideal.absNorm 𝔪.ideal with hN`. Establish `hN0 : N ≠ 0`. Rewrite using `[hN, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `𝔪.ideal_ne_bot`.

Use `haveI : NeZero N := ⟨hN0⟩`. Establish `hcyc` using `cyc_adjoin ℚ hζ`. Use `haveI : NumberField ℚ⟮ζ⟯ := @IsCyclotomicExtension.numberField {N} ℚ ℚ⟮ζ⟯ _ _ _ _ _ hcyc`. Establish `hgal` using `@IsCyclotomicExtension.isGalois {N} ℚ ℚ⟮ζ⟯ _ _ _ hcyc`. Use `haveI := (GroundTheory.Global.Modulus.isAbelianGalois_rayClassField 𝔪 Ω).toIsGalois`.

Establish `hfin : ({v | v.asIdeal ∣ 𝔪.ideal} ∪ {v | v.asIdeal ∣ Ideal.span {(N : 𝓞 ℚ)}} : Set (HeightOneSpectrum (𝓞 ℚ))).Finite`. Use `(Ideal.finite_factors 𝔪.ideal_ne_bot).union (Ideal.finite_factors ?_)` and prove the remaining obligations. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN0` after adjusting the coercions. Use `@UpperTheory.V.CF.bauer ℚ Ω _ _ _ _ (𝔪.rayClassField Ω) ℚ⟮ζ⟯ _ _ _ (by convert hgal; exact Subsingleton.elim _ _) _ hfin ?_` and prove the remaining obligations.

Introduce `v hv hsplit`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or] at hv`. Take `⟨_, hv2⟩` from `hv`. Rewrite `hv2` using `[Ideal.dvd_span_singleton]`. Take `⟨p, hp, hpv⟩` from `exists_prime_mem_of_mem v.asIdeal v.isPrime (Ideal.absNorm v.asIdeal) (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot) (Ideal.absNorm_mem _)`.

Establish `hpN : ¬ p ∣ N`. Introduce and unpack `⟨k, hk⟩`. Apply `hv2` to reduce the goal to its premises. Rewrite using `[hk, Nat.cast_mul]`. Conclude with `v.asIdeal.mul_mem_right _ hpv`.

Establish `hmod : p ≡ 1 [MOD N]` using `by haveI hc2 : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := by`. Use `hcyc` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `exact Subsingleton.elim _ _`.

Use `UpperTheory.V.CF.splitCyc N ℚ⟮ζ⟯ v p hp hpv hpN ?_` and prove the remaining obligations. Use `hsplit` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `exact Subsingleton.elim _ _`.

Take `⟨hv', hcls⟩` from `UpperTheory.V.CF.rayPrime 𝔪 v p hp hpv hmod`. Conclude with `(GroundTheory.Global.Modulus.splitsCompletely_rayClassField_iff 𝔪 Ω hv').mpr hcls`.
-/
theorem UpperTheory.V.CF.kwRay :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (𝔪 : GroundTheory.Global.Modulus ℚ) (ζ : Ω), IsPrimitiveRoot ζ (Ideal.absNorm 𝔪.ideal) → 𝔪.rayClassField Ω ≤ ℚ⟮ζ⟯ := by
  intro Ω _ _ _ 𝔪 ζ hζ
  set N := Ideal.absNorm 𝔪.ideal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]
    exact 𝔪.ideal_ne_bot
  haveI : NeZero N := ⟨hN0⟩
  have hcyc := cyc_adjoin ℚ hζ
  haveI : NumberField ℚ⟮ζ⟯ := @IsCyclotomicExtension.numberField {N} ℚ ℚ⟮ζ⟯ _ _ _ _ _ hcyc
  have hgal := @IsCyclotomicExtension.isGalois {N} ℚ ℚ⟮ζ⟯ _ _ _ hcyc
  haveI := (GroundTheory.Global.Modulus.isAbelianGalois_rayClassField 𝔪 Ω).toIsGalois
  have hfin : ({v | v.asIdeal ∣ 𝔪.ideal} ∪ {v | v.asIdeal ∣ Ideal.span {(N : 𝓞 ℚ)}} :
      Set (HeightOneSpectrum (𝓞 ℚ))).Finite := by
    refine (Ideal.finite_factors 𝔪.ideal_ne_bot).union (Ideal.finite_factors ?_)
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  refine @UpperTheory.V.CF.bauer ℚ Ω _ _ _ _ (𝔪.rayClassField Ω) ℚ⟮ζ⟯ _ _ _
    (by convert hgal; exact Subsingleton.elim _ _) _ hfin ?_
  intro v hv hsplit
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hv
  obtain ⟨_, hv2⟩ := hv
  rw [Ideal.dvd_span_singleton] at hv2
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_of_mem v.asIdeal v.isPrime
    (Ideal.absNorm v.asIdeal) (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    (Ideal.absNorm_mem _)
  have hpN : ¬ p ∣ N := by
    rintro ⟨k, hk⟩
    apply hv2
    rw [hk, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv
  have hmod : p ≡ 1 [MOD N] := by
    haveI hc2 : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := by
      convert hcyc
      all_goals first
        | rfl
        | exact Subsingleton.elim _ _
    refine UpperTheory.V.CF.splitCyc N ℚ⟮ζ⟯ v p hp hpv hpN ?_
    convert hsplit
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
  obtain ⟨hv', hcls⟩ := UpperTheory.V.CF.rayPrime 𝔪 v p hp hpv hmod
  exact (GroundTheory.Global.Modulus.splitsCompletely_rayClassField_iff 𝔪 Ω hv').mpr hcls
