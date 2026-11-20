import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Imports

open NumberField Pointwise

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CuspFormEvaluationSupplement.main`. Consider the case `exact _root_.GlobalTheory.CuspFormEvaluationSupplement.main`. Consider the case `(apply _root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CuspFormEvaluationSupplement.main ..)`.
-/
theorem exists_prime_dvd_natCast_mem {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime) :
    ∀ N : ℕ, N ≠ 0 → (N : R) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ (p : R) ∈ P := by
  first
  | exact @_root_.GlobalTheory.CuspFormEvaluationSupplement.main
  | exact _root_.GlobalTheory.CuspFormEvaluationSupplement.main
  | (apply _root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CuspFormEvaluationSupplement.main ..)

/- English proof (translation)
Establish `: IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E)` using `IsGaloisGroup.of_isFractionRing (E ≃ₐ[ℚ] E) ℤ (𝓞 E) ℚ E`. Use `set D := differentIdeal ℤ (𝓞 E) with hD`. Establish `hD0 : D ≠ 0` using `differentIdeal_ne_bot`. Establish `hspan : ∀ M : ℕ, M ≠ 0 → Ideal.span {((M : ℕ) : 𝓞 E)} ≠ 0` using `fun M hM => by`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `Nat.cast_ne_zero.2 hM`. Rewrite using `[UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (hspan N hN0.ne')]`. Introduce `P hP`. Distinguish the cases in `hPN : P ∣ Ideal.span {((N : ℕ) : 𝓞 E)}`. Use `swap`.

Rewrite using `[emultiplicity_eq_zero.2 hPN]`. Conclude with `zero_le`. Establish `hPp : P.IsPrime` using `Ideal.isPrime_of_prime hP`. Take `⟨p, hp, ⟨M, rfl⟩, hpP⟩` from `exists_prime_dvd_natCast_mem hPp N hN0.ne' (Ideal.dvd_span_singleton.1 hPN)`. Establish `hM0 : 0 < M` using `Nat.pos_of_mul_pos_left hN0`.

Establish `hMD` using `hmin M hM0 ((Nat.lt_mul_iff_one_lt_left hM0).2 hp.one_lt)`. Rewrite `hMD` using `[← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0]`. Use `push Not at hMD`. Take `⟨Q, hQ, hQlt⟩` from `hMD`. Establish `hQp : Q.IsPrime` using `Ideal.isPrime_of_prime hQ`.

Establish `hmul : Ideal.span {((p * M : ℕ) : 𝓞 E)} = Ideal.span {(p : 𝓞 E)} * Ideal.span {(M : 𝓞 E)}`. Rewrite using `[Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]`. Establish `hpQ : (p : 𝓞 E) ∈ Q`. Assume the negation of the conclusion as `h`. Establish `h1` using `emultiplicity_le_emultiplicity_of_dvd_right (a := Q) (Ideal.dvd_span_singleton.2 hN)`.

Establish `h2 : emultiplicity Q (Ideal.span {(p : 𝓞 E)}) = 0` using `emultiplicity_eq_zero.2 fun hh => h (Ideal.dvd_span_singleton.1 hh)`. Rewrite `h1` using `[hmul, emultiplicity_mul hQ, h2, zero_add]`. Conclude with `absurd hQlt (not_lt.2 h1)`. Use `liesOver_span E p hp hPp hpP` as an intermediate fact. Use `liesOver_span E p hp hQp hpQ` as an intermediate fact.

Take `⟨σ, rfl⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)`. Establish `h3 : ∀ X : Ideal (𝓞 E), σ • X = X → emultiplicity (σ • P) X = emultiplicity P X` using `fun X hX => by conv_lhs => rw [← hX]`. Conclude with `emultiplicity_map_eq (MulSemiringAction.toRingEquiv (E ≃ₐ[ℚ] E) (Ideal (𝓞 E)) σ)`. Rewrite `hQlt` using `[h3 _ (smul_span_nat σ M), h3 _ (smul_differentIdeal σ)]`. Establish `fD` using `FiniteMultiplicity.of_prime_left hP hD0`.

Establish `fM` using `FiniteMultiplicity.of_prime_left hP (hspan M hM0.ne')`. Establish `fp` using `FiniteMultiplicity.of_prime_left hP (hspan p hp.ne_zero)`. Establish `hpmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Establish `hp0 : Ideal.span {(p : ℤ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hd : P ^ (multiplicity P (Ideal.span {(p : 𝓞 E)}) - 1) ∣ D`. Use `pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) P _ hp0 ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Conclude with `pow_multiplicity_dvd _ _`.

Establish `hd'` using `fD.le_multiplicity_of_pow_dvd hd`. Rewrite using `[hmul, emultiplicity_mul hP, pow_two, emultiplicity_mul hP]`. Rewrite `hQlt`, the goal using `[fD.emultiplicity_eq_multiplicity, fM.emultiplicity_eq_multiplicity]`. Rewrite using `[fp.emultiplicity_eq_multiplicity]`. Normalize the coercions in `at hQlt ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
theorem span_natCast_dvd_differentIdeal_sq (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (N : ℕ)
    (hN0 : 0 < N) (hN : ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E))
    (hmin : ∀ M : ℕ, 0 < M → M < N → ((M : ℕ) : 𝓞 E) ∉ differentIdeal ℤ (𝓞 E)) :
    Ideal.span {((N : ℕ) : 𝓞 E)} ∣ differentIdeal ℤ (𝓞 E) ^ 2 := by
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing (E ≃ₐ[ℚ] E) ℤ (𝓞 E) ℚ E
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hD0 : D ≠ 0 := differentIdeal_ne_bot
  have hspan : ∀ M : ℕ, M ≠ 0 → Ideal.span {((M : ℕ) : 𝓞 E)} ≠ 0 := fun M hM => by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hM
  rw [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (hspan N hN0.ne')]
  intro P hP
  by_cases hPN : P ∣ Ideal.span {((N : ℕ) : 𝓞 E)}
  swap
  · rw [emultiplicity_eq_zero.2 hPN]
    exact zero_le
  have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
  obtain ⟨p, hp, ⟨M, rfl⟩, hpP⟩ := exists_prime_dvd_natCast_mem hPp N hN0.ne' (Ideal.dvd_span_singleton.1 hPN)
  have hM0 : 0 < M := Nat.pos_of_mul_pos_left hN0
  have hMD := hmin M hM0 ((Nat.lt_mul_iff_one_lt_left hM0).2 hp.one_lt)
  rw [← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0] at hMD
  push Not at hMD
  obtain ⟨Q, hQ, hQlt⟩ := hMD
  have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
  have hmul : Ideal.span {((p * M : ℕ) : 𝓞 E)} = Ideal.span {(p : 𝓞 E)} * Ideal.span {(M : 𝓞 E)} := by
    rw [Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]
  have hpQ : (p : 𝓞 E) ∈ Q := by
    by_contra h
    have h1 := emultiplicity_le_emultiplicity_of_dvd_right (a := Q) (Ideal.dvd_span_singleton.2 hN)
    have h2 : emultiplicity Q (Ideal.span {(p : 𝓞 E)}) = 0 :=
      emultiplicity_eq_zero.2 fun hh => h (Ideal.dvd_span_singleton.1 hh)
    rw [hmul, emultiplicity_mul hQ, h2, zero_add] at h1
    exact absurd hQlt (not_lt.2 h1)
  have := liesOver_span E p hp hPp hpP
  have := liesOver_span E p hp hQp hpQ
  obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have h3 : ∀ X : Ideal (𝓞 E), σ • X = X → emultiplicity (σ • P) X = emultiplicity P X := fun X hX => by
    conv_lhs => rw [← hX]
    exact emultiplicity_map_eq (MulSemiringAction.toRingEquiv (E ≃ₐ[ℚ] E) (Ideal (𝓞 E)) σ)
  rw [h3 _ (smul_span_nat σ M), h3 _ (smul_differentIdeal σ)] at hQlt
  have fD := FiniteMultiplicity.of_prime_left hP hD0
  have fM := FiniteMultiplicity.of_prime_left hP (hspan M hM0.ne')
  have fp := FiniteMultiplicity.of_prime_left hP (hspan p hp.ne_zero)
  have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  have hd : P ^ (multiplicity P (Ideal.span {(p : 𝓞 E)}) - 1) ∣ D := by
    refine pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) P _ hp0 ?_
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact pow_multiplicity_dvd _ _
  have hd' := fD.le_multiplicity_of_pow_dvd hd
  rw [hmul, emultiplicity_mul hP, pow_two, emultiplicity_mul hP]
  rw [fD.emultiplicity_eq_multiplicity, fM.emultiplicity_eq_multiplicity] at hQlt ⊢
  rw [fp.emultiplicity_eq_multiplicity]
  norm_cast at hQlt ⊢
  omega

/- English proof (translation)
Introduce `E _ _ _`. Establish `hd0 : (NumberField.discr E).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)`. Establish `hex : ∃ N : ℕ, 0 < N ∧ ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)`. Use `⟨(NumberField.discr E).natAbs, Nat.pos_of_ne_zero hd0, ?_⟩` and prove the remaining obligations. Rewrite using `[← NumberField.absNorm_differentIdeal E (𝓞 E)]`.

Conclude with `Ideal.absNorm_mem _`. Take `⟨h0, hmem⟩` from `Nat.find_spec hex`. Use `⟨Nat.find hex, h0, hmem, ?_⟩` and prove the remaining obligations. Establish `hdvd` using `span_natCast_dvd_differentIdeal_sq E _ h0 hmem fun M hM hlt hMD => Nat.find_min hex hlt ⟨hM, hMD⟩`. Establish `h1` using `map_dvd Ideal.absNorm hdvd`.

Rewrite `h1` using `[absNorm_span_nat, map_pow, NumberField.absNorm_differentIdeal E (𝓞 E)]`. Establish `h2` using `Nat.le_of_dvd (Nat.pos_of_ne_zero (pow_ne_zero 2 hd0)) h1`. Establish `h3 : |(NumberField.discr E : ℝ)| = ((NumberField.discr E).natAbs : ℝ)`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`. Rewrite using `[h3]`.

Conclude with `h2` after adjusting the coercions.
-/
theorem exists_natCast_mem_differentIdeal_pow_le :
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], ∃ N : ℕ, 0 < N ∧
      ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) ∧
      (N : ℝ) ^ Module.finrank ℚ E ≤ |(NumberField.discr E : ℝ)| ^ 2 := by
  intro E _ _ _
  classical
  have hd0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
  have hex : ∃ N : ℕ, 0 < N ∧ ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := by
    refine ⟨(NumberField.discr E).natAbs, Nat.pos_of_ne_zero hd0, ?_⟩
    rw [← NumberField.absNorm_differentIdeal E (𝓞 E)]
    exact Ideal.absNorm_mem _
  obtain ⟨h0, hmem⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h0, hmem, ?_⟩
  have hdvd := span_natCast_dvd_differentIdeal_sq E _ h0 hmem
    fun M hM hlt hMD => Nat.find_min hex hlt ⟨hM, hMD⟩
  have h1 := map_dvd Ideal.absNorm hdvd
  rw [absNorm_span_nat, map_pow, NumberField.absNorm_differentIdeal E (𝓞 E)] at h1
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (pow_ne_zero 2 hd0)) h1
  have h3 : |(NumberField.discr E : ℝ)| = ((NumberField.discr E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h3]
  exact_mod_cast h2

end GlobalTheory
