import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RootDVR

/- English proof (translation)
Introduce `p hp m hm`. Take `⟨y, hy⟩` from `IsAlgClosed.exists_pow_nat_eq ((p : ℚ) : AlgebraicClosure ℚ) (by omega : 0 < m)`. Set `K` to `IntermediateField.adjoin ℚ ({y} : Set (AlgebraicClosure ℚ))`. Use `haveI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)`. Use `haveI : NumberField K := ⟨⟩`.

Set `x : K` to `⟨y, IntermediateField.subset_adjoin ℚ _ rfl⟩`. Establish `hx : x ^ m = (p : K)` using `Subtype.ext (by simpa [x] using hy)`. Establish `hxint : IsIntegral ℤ x`. Use `⟨X ^ m - C (p : ℤ), monic_X_pow_sub_C _ (by omega), ?_⟩` and prove the remaining obligations. Simplify using `[hx]`.

Set `a : 𝓞 K` to `⟨x, hxint⟩`. Establish `ha : a ^ m = (p : 𝓞 K)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `first`. Consider the case `(rw [RingOfIntegers.coe_pow]; exact hx)`.

Consider the case `(push_cast; exact hx)`. Consider the case `(simp only [map_pow, map_natCast]; exact hx)`. Consider the case `exact hx`. Establish `hP0 : (Ideal.span {(p : ℤ)}).IsMaximal` using `Int.ideal_span_isMaximal_of_prime p`. Establish `hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(p : ℤ)}`.

Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]`. Conclude with `bot_le`. Take `⟨P, hPmax, hPc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral _ hker`. Establish `hpP : (p : 𝓞 K) ∈ P`. Establish `: (p : ℤ) ∈ P.comap (algebraMap ℤ (𝓞 K))` using `hPc ▸ Ideal.subset_span rfl`.

Simplify using `using this`. Set `v : HeightOneSpectrum (𝓞 K)` to `⟨P, hPmax.isPrime, fun h => by`. Rewrite `hpP` using `[h, Ideal.mem_bot]`. Conclude with `(Fact.out : p.Prime).ne_zero (by exact_mod_cast hpP)⟩`. Set `O` to `v.valuationSubringAtPrime K`.

Establish `hdvr : IsDiscreteValuationRing O` using `(isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime K v (Ring.HasFiniteQuotients.finiteQuotient v.ne_bot)).1`. Use `haveI : IsLocalization v.asIdeal.primeCompl O := Localization.subalgebra.isLocalization_ofField K v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors`. Establish `hpO : (p : O) ∈ maximalIdeal O`. Use `(IsLocalization.AtPrime.to_map_mem_maximal_iff O v.asIdeal (p : 𝓞 K)).mpr hpP` as an intermediate fact. Simplify using `using this`.

Establish `hres : CharP (ResidueField O) p`. Rewrite using `[CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]`. Rewrite using `[← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]`. Conclude with `hpO`. Use `⟨O, inferInstance, inferInstance, hdvr, ⟨fun u w h => by` and prove the remaining obligations.

Establish `h'` using `congrArg (fun z : O => (z : K)) h`. Conclude with `h'⟩, hres,` after adjusting the coercions. Use `algebraMap (𝓞 K) O a, ?_⟩`. Rewrite using `[← map_pow, ha, map_natCast]`.
-/
theorem exists_dvr_pow_eq_prime : ∀ (p : ℕ) [Fact p.Prime] (m : ℕ), 1 ≤ m → ∃ (O : Type) (_ : CommRing O)
    (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : CharZero O) (_ : CharP (ResidueField O) p)
    (ϖ : O), ϖ ^ m = p := by
  intro p hp m hm
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℚ) : AlgebraicClosure ℚ) (by omega : 0 < m)
  let K := IntermediateField.adjoin ℚ ({y} : Set (AlgebraicClosure ℚ))
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  haveI : NumberField K := ⟨⟩
  let x : K := ⟨y, IntermediateField.subset_adjoin ℚ _ rfl⟩
  have hx : x ^ m = (p : K) := Subtype.ext (by simpa [x] using hy)
  have hxint : IsIntegral ℤ x := by
    refine ⟨X ^ m - C (p : ℤ), monic_X_pow_sub_C _ (by omega), ?_⟩
    simp [hx]
  let a : 𝓞 K := ⟨x, hxint⟩
  have ha : a ^ m = (p : 𝓞 K) := by
    apply RingOfIntegers.ext
    first
      | (rw [RingOfIntegers.coe_pow]; exact hx)
      | (push_cast; exact hx)
      | (simp only [map_pow, map_natCast]; exact hx)
      | exact hx
  have hP0 : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(p : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]
    exact bot_le
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral _ hker
  have hpP : (p : 𝓞 K) ∈ P := by
    have : (p : ℤ) ∈ P.comap (algebraMap ℤ (𝓞 K)) := hPc ▸ Ideal.subset_span rfl
    simpa using this
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, hPmax.isPrime, fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hpP)⟩
  let O := v.valuationSubringAtPrime K
  have hdvr : IsDiscreteValuationRing O :=
    (isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime K v
      (Ring.HasFiniteQuotients.finiteQuotient v.ne_bot)).1
  haveI : IsLocalization v.asIdeal.primeCompl O :=
    Localization.subalgebra.isLocalization_ofField K v.asIdeal.primeCompl
      v.asIdeal.primeCompl_le_nonZeroDivisors
  have hpO : (p : O) ∈ maximalIdeal O := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O v.asIdeal (p : 𝓞 K)).mpr hpP
    simpa using this
  have hres : CharP (ResidueField O) p := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact hpO
  refine ⟨O, inferInstance, inferInstance, hdvr,
    ⟨fun u w h => by
      have h' := congrArg (fun z : O => (z : K)) h
      exact_mod_cast h'⟩, hres,
    algebraMap (𝓞 K) O a, ?_⟩
  rw [← map_pow, ha, map_natCast]

end GlobalTheory.RootDVR
