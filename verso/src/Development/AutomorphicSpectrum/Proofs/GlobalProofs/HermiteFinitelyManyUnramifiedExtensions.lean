import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePowerStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RamifiedPrimeContainsDiscriminantStatement

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.HermiteMinkowski

noncomputable def bound {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  (discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm

/- English proof (translation)
Use `mul_ne_zero (Int.natAbs_ne_zero.mpr (discr_ne_zero F)) ?_` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.mpr fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`.
-/
theorem bound_ne_zero {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : bound S ≠ 0 := by
  refine mul_ne_zero (Int.natAbs_ne_zero.mpr (discr_ne_zero F)) ?_
  refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

/- English proof (translation)
Establish `hdvd` using `GlobalTheory.T.different_dvd_ramified_prime_power E (bound S) (bound_ne_zero S) fun P hP hP0 hPd => by haveI := hP`. Conclude with `GlobalTheory.T.ramified_prime_contains_discriminant F E S hE P hP0 hPd`. Establish `h` using `map_dvd Ideal.absNorm hdvd`. Rewrite `h` using `[absNorm_differentIdeal E (𝓞 E)]`. Establish `hr : ((bound S : 𝓞 E)) ^ (Module.finrank ℚ E) = algebraMap ℤ (𝓞 E) (((bound S : ℕ) : ℤ) ^ (Module.finrank ℚ E))`.

Simplify using the standard rewrite rules. Rewrite `h` using `[Ideal.absNorm_span_singleton, hr, Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul]`. Conclude with `h`.
-/
theorem natAbs_discr_dvd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hE : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) :
    (discr E).natAbs ∣ bound S ^ (Module.finrank ℚ E * Module.finrank ℚ E) := by
  have hdvd := GlobalTheory.T.different_dvd_ramified_prime_power E (bound S) (bound_ne_zero S) fun P hP hP0 hPd => by
    haveI := hP
    exact GlobalTheory.T.ramified_prime_contains_discriminant F E S hE P hP0 hPd
  have h := map_dvd Ideal.absNorm hdvd
  rw [absNorm_differentIdeal E (𝓞 E)] at h
  have hr : ((bound S : 𝓞 E)) ^ (Module.finrank ℚ E) =
      algebraMap ℤ (𝓞 E) (((bound S : ℕ) : ℤ) ^ (Module.finrank ℚ E)) := by
    simp
  rw [Ideal.absNorm_span_singleton, hr, Algebra.norm_algebraMap, RingOfIntegers.rank,
    Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul] at h
  exact h

end GlobalTheory.CompanionTheory.HermiteMinkowski

open GlobalTheory.CompanionTheory.HermiteMinkowski in
/- English proof (translation)
Introduce `F Ω _ _ _ _ _ S N`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `set n := Module.finrank ℚ F * N with hn`. Use `set M : ℕ := bound S ^ (n * n) with hM`. Establish `hfin` using `(NumberField.finite_of_discr_bdd Ω M).image Subtype.val`.

Establish `hinj : Function.Injective (fun E : IntermediateField F Ω => E.restrictScalars ℚ)` using `IntermediateField.restrictScalars_injective ℚ`. Use `(hfin.preimage hinj.injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `E ⟨hfd, hun, hdeg⟩`. Use `haveI := hfd`. Use `haveI : NumberField E := NumberField.of_module_finite F E`.

Set `e : (E.restrictScalars ℚ) ≃ₐ[ℚ] E` to `(RingEquiv.refl E : E ≃+* E).toRatAlgEquiv`. Use `haveI hfd' : FiniteDimensional ℚ (E.restrictScalars ℚ) := e.toLinearEquiv.symm.finiteDimensional`. Use `⟨⟨E.restrictScalars ℚ, hfd'⟩, ?_, rfl⟩` and prove the remaining obligations. Use `haveI : NumberField (E.restrictScalars ℚ) := @NumberField.mk _ _ inferInstance hfd'`. Use `show |discr (E.restrictScalars ℚ)| ≤ (M : ℤ)`.

Rewrite using `[discr_eq_discr_of_algEquiv _ e]`. Establish `hdvd` using `natAbs_discr_dvd (E := E) S fun v hv => hun v (by simpa using hv)`. Establish `hd : Module.finrank ℚ E ≤ n`. Rewrite using `[← Module.finrank_mul_finrank ℚ F E]`. Conclude with `Nat.mul_le_mul_left _ hdeg`.

Establish `hb : 0 < bound S` using `Nat.pos_of_ne_zero (bound_ne_zero S)`. Establish `hle` using `Nat.le_of_dvd (pow_pos hb _) hdvd`. Establish `hle2 : bound S ^ (Module.finrank ℚ E * Module.finrank ℚ E) ≤ bound S ^ (n * n)` using `Nat.pow_le_pow_right hb (Nat.mul_le_mul hd hd)`. Rewrite using `[hM, Int.abs_eq_natAbs]`. Conclude with `hle.trans hle2` after adjusting the coercions.
-/
theorem GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ),
      {E : IntermediateField F Ω | FiniteDimensional F E ∧
        IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧
        Module.finrank F E ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S N
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  set n := Module.finrank ℚ F * N with hn
  set M : ℕ := bound S ^ (n * n) with hM
  have hfin := (NumberField.finite_of_discr_bdd Ω M).image Subtype.val
  have hinj : Function.Injective (fun E : IntermediateField F Ω => E.restrictScalars ℚ) :=
    IntermediateField.restrictScalars_injective ℚ
  refine (hfin.preimage hinj.injOn).subset ?_
  rintro E ⟨hfd, hun, hdeg⟩
  haveI := hfd
  haveI : NumberField E := NumberField.of_module_finite F E
  let e : (E.restrictScalars ℚ) ≃ₐ[ℚ] E := (RingEquiv.refl E : E ≃+* E).toRatAlgEquiv
  haveI hfd' : FiniteDimensional ℚ (E.restrictScalars ℚ) :=
    e.toLinearEquiv.symm.finiteDimensional
  refine ⟨⟨E.restrictScalars ℚ, hfd'⟩, ?_, rfl⟩
  haveI : NumberField (E.restrictScalars ℚ) := @NumberField.mk _ _ inferInstance hfd'
  show |discr (E.restrictScalars ℚ)| ≤ (M : ℤ)
  rw [discr_eq_discr_of_algEquiv _ e]
  have hdvd := natAbs_discr_dvd (E := E) S fun v hv => hun v (by simpa using hv)
  have hd : Module.finrank ℚ E ≤ n := by
    rw [← Module.finrank_mul_finrank ℚ F E]
    exact Nat.mul_le_mul_left _ hdeg
  have hb : 0 < bound S := Nat.pos_of_ne_zero (bound_ne_zero S)
  have hle := Nat.le_of_dvd (pow_pos hb _) hdvd
  have hle2 : bound S ^ (Module.finrank ℚ E * Module.finrank ℚ E) ≤ bound S ^ (n * n) :=
    Nat.pow_le_pow_right hb (Nat.mul_le_mul hd hd)
  rw [hM, Int.abs_eq_natAbs]
  exact_mod_cast hle.trans hle2
