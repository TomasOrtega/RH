import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

namespace GlobalTheory.CyclotomicCompletion

/- English proof (translation)
Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.1 hl`. Establish `: (Ideal.span {(l : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hp.ne_zero).2 hp`. Take `⟨Q, hQ, hQ'⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (Ideal.span {(l : ℤ)}) (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int (algebraMap ℤ (𝓞 K)))]`. Conclude with `bot_le)`.

Establish `hmem : (l : 𝓞 K) ∈ Q`. Establish `: (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K))`. Rewrite using `[hQ']`. Conclude with `Ideal.mem_span_singleton_self _`. Simplify `this` using `[Ideal.mem_comap]`.

Use `⟨⟨Q, hQ, ?_⟩, hmem⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hl.ne_zero (by simpa using hmem)`.
-/
theorem exists_place_above (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := 𝓞 K) (Ideal.span {(l : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int (algebraMap ℤ (𝓞 K)))]; exact bot_le)
  have hmem : (l : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      rw [hQ']; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  rintro rfl
  exact hl.ne_zero (by simpa using hmem)

/- English proof (translation)
Introduce `l hl`. Establish `: NeZero l` using `⟨hl.ne_zero⟩`. Set `K : Type` to `CyclotomicField l ℚ`. Take `⟨v, hv⟩` from `exists_place_above K hl`. Establish `hinj : Function.Injective (algebraMap (𝓞 K) (v.adicCompletionIntegers K))` using `FaithfulSMul.algebraMap_injective _ _`.

Establish `hc : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)`. Use `NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion K) ⟨?_, ?_, ?_⟩ (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top` and prove the remaining obligations. Conclude with `FaithfulSMul.algebraMap_injective _ _`. Introduce `x`. Establish `: ‖(x : v.adicCompletion K)‖ ≤ 1` using `Valued.toNormedField.norm_le_one_iff.2 x.2`.

Conclude with `this` after adjusting the coercions. Introduce `x hx`. Establish `: ‖x‖ ≤ 1` using `by exact_mod_cast hx`. Conclude with `⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩`. Use `⟨v.adicCompletionIntegers K, inferInstance, inferInstance, inferInstance, hc, charZero_of_injective_algebraMap hinj, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_natCast (algebraMap (𝓞 K) (v.adicCompletionIntegers K)), adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem]`. Conclude with `fun h => h hv`. Establish `: IsCyclotomicExtension {l} ℚ K` using `CyclotomicField.isCyclotomicExtension l ℚ`. Establish `hζ` using `IsCyclotomicExtension.zeta_spec l ℚ K`. Conclude with `⟨_, hζ.toInteger_isPrimitiveRoot.map_of_injective hinj⟩`.
-/
theorem exists_complete_dvr_primitiveRoot : ∀ l : ℕ, l.Prime → ∃ (O : Type) (_ : CommRing O)
    (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (_ : CharZero O),
    ¬ IsUnit (l : O) ∧ ∃ ζ : O, IsPrimitiveRoot ζ l := by
  intro l hl
  have : NeZero l := ⟨hl.ne_zero⟩
  let K : Type := CyclotomicField l ℚ
  obtain ⟨v, hv⟩ := exists_place_above K hl
  have hinj : Function.Injective (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hc : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) := by
    refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion K) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion K)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  refine ⟨v.adicCompletionIntegers K, inferInstance, inferInstance, inferInstance, hc,
    charZero_of_injective_algebraMap hinj, ?_, ?_⟩
  · rw [← map_natCast (algebraMap (𝓞 K) (v.adicCompletionIntegers K)),
      adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply,
      valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem]
    exact fun h => h hv
  · have : IsCyclotomicExtension {l} ℚ K := CyclotomicField.isCyclotomicExtension l ℚ
    have hζ := IsCyclotomicExtension.zeta_spec l ℚ K
    exact ⟨_, hζ.toInteger_isPrimitiveRoot.map_of_injective hinj⟩

end GlobalTheory.CyclotomicCompletion
