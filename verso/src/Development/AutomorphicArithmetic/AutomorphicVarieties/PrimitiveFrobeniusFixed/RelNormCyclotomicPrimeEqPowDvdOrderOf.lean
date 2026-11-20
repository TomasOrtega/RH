import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.Ideal.Norm.RelNorm

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Introduce `N r _ K K' _ _ _ _ _ _ hp hN v v' hr hvv`. Establish `: Fact r.Prime` using `⟨hp⟩`. Establish `hvp : v'.asIdeal.IsPrime` using `v'.isPrime`. Establish `hm : v.asIdeal.IsMaximal` using `v.isMaximal`. Establish `hm' : v'.asIdeal.IsMaximal` using `v'.isMaximal`.

Establish `hmax : (Ideal.span {(r : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Establish `hlo : v'.asIdeal.LiesOver (Ideal.span {(r : ℤ)})`. Use `⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]`. Conclude with `hr`.

Establish `hl2 : v'.asIdeal.LiesOver v.asIdeal` using `⟨by`. Use extensionality with `y`. Rewrite using `[Ideal.under_def, Ideal.mem_comap]`. Conclude with `(hvv y).symm⟩`. Establish `h3` using `Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal v'.asIdeal`.

Rewrite `h3` using `[IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd r K' v'.asIdeal hN]`. Use `⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h3]`. Conclude with `Dvd.intro_left _ rfl`. Conclude with `Ideal.relNorm_eq_pow_of_isMaximal v'.asIdeal v.asIdeal`.
-/
theorem UpperTheory.relNorm_cyclotomic_prime_eq_pow_dvd_orderOf :
    ∀ (N r : ℕ) [NeZero N] (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] [Algebra K K'], r.Prime → ¬ r ∣ N → ∀ (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 K')), (r : 𝓞 K') ∈ v'.asIdeal → (∀ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 K') y ∈ v'.asIdeal ↔ y ∈ v.asIdeal) → ∃ s : ℕ, s ∣ orderOf (r : ZMod N) ∧ Ideal.relNorm (𝓞 K) v'.asIdeal = v.asIdeal ^ s := by
  intro N r _ K K' _ _ _ _ _ _ hp hN v v' hr hvv
  have : Fact r.Prime := ⟨hp⟩
  have hvp : v'.asIdeal.IsPrime := v'.isPrime
  have hm : v.asIdeal.IsMaximal := v.isMaximal
  have hm' : v'.asIdeal.IsMaximal := v'.isMaximal
  have hmax : (Ideal.span {(r : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hlo : v'.asIdeal.LiesOver (Ideal.span {(r : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hr
  have hl2 : v'.asIdeal.LiesOver v.asIdeal := ⟨by
    ext y
    rw [Ideal.under_def, Ideal.mem_comap]
    exact (hvv y).symm⟩
  have h3 := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal v'.asIdeal
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd r K' v'.asIdeal hN] at h3
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_, ?_⟩
  · rw [h3]; exact Dvd.intro_left _ rfl
  · exact Ideal.relNorm_eq_pow_of_isMaximal v'.asIdeal v.asIdeal
