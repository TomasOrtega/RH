import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

open NumberField IsDedekindDomain IsLocalRing HeightOneSpectrum

namespace GlobalTheory.CompleteDVR

/- English proof (translation)
Establish `hint : ∀ a : 𝓞 K, (a : K) ∈ W` using `fun a => by`. Establish `h2 : IsIntegral W (a : K)` using `(RingOfIntegers.isIntegral_coe a).tower_top`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := W) (K := K)).mp h2`. Rewrite using `[← hy]`. Conclude with `y.2`.

Set `g : 𝓞 K →+* W` to `(algebraMap (𝓞 K) K).codRestrict W hint`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal W).comap g) (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal W).ne_top)`. Use `⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨n, d, hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha`. Establish `hu : IsUnit (g d)`.

Assume the negation of the conclusion as `hu`. Conclude with `d.2 (hle ((IsLocalRing.mem_maximalIdeal _).2 hu))`. Take `⟨b, hb⟩` from `hu.exists_right_inv`. Establish `hb' : algebraMap (𝓞 K) K d * (b : K) = 1` using `congrArg Subtype.val hb`. Establish `: a = algebraMap (𝓞 K) K n * (b : K)` using `by rw [← hnd, mul_assoc, hb', mul_one]`.

Rewrite using `[this]`. Conclude with `W.mul_mem _ _ (hint n) b.2`.
-/
theorem exists_place_le {K : Type} [Field K] [NumberField K] (W : ValuationSubring K) :
    ∃ la : HeightOneSpectrum (𝓞 K), (la.valuation K).valuationSubring ≤ W := by
  have hint : ∀ a : 𝓞 K, (a : K) ∈ W := fun a => by
    have h2 : IsIntegral W (a : K) := (RingOfIntegers.isIntegral_coe a).tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := K)).mp h2
    rw [← hy]
    exact y.2
  let g : 𝓞 K →+* W := (algebraMap (𝓞 K) K).codRestrict W hint
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal W).comap g)
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal W).ne_top)
  refine ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩,
    fun a ha => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha
  have hu : IsUnit (g d) := by
    by_contra hu
    exact d.2 (hle ((IsLocalRing.mem_maximalIdeal _).2 hu))
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : algebraMap (𝓞 K) K d * (b : K) = 1 := congrArg Subtype.val hb
  have : a = algebraMap (𝓞 K) K n * (b : K) := by rw [← hnd, mul_assoc, hb', mul_one]
  rw [this]
  exact W.mul_mem _ _ (hint n) b.2

/- English proof (translation)
Introduce `h`. Establish `hall : ∀ y : K, y ∈ V` using `fun y => h ▸ ValuationSubring.mem_top y`. Apply `IsDiscreteValuationRing.not_a_field V` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [Ideal.mem_bot]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Assume the negation of the conclusion as `hne`. Establish `hne' : (x : K) ≠ 0` using `fun h0 => hne (Subtype.ext h0)`. Apply `(IsLocalRing.mem_maximalIdeal x).1 hx` to reduce the goal to its premises.

Use `IsUnit.of_mul_eq_one ⟨(x : K)⁻¹, hall _⟩ (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `[hne']`. Introduce and unpack `rfl`. Conclude with `Ideal.zero_mem _`.
-/
theorem ne_top_of_isDiscreteValuationRing {K : Type} [Field K] (V : ValuationSubring K)
    [IsDiscreteValuationRing V] : V ≠ ⊤ := by
  intro h
  have hall : ∀ y : K, y ∈ V := fun y => h ▸ ValuationSubring.mem_top y
  apply IsDiscreteValuationRing.not_a_field V
  ext x
  simp only [Ideal.mem_bot]
  constructor
  · intro hx
    by_contra hne
    have hne' : (x : K) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    apply (IsLocalRing.mem_maximalIdeal x).1 hx
    refine IsUnit.of_mul_eq_one ⟨(x : K)⁻¹, hall _⟩ (Subtype.ext ?_)
    simp [hne']
  · rintro rfl
    exact Ideal.zero_mem _

/- English proof (translation)
Introduce `F _ _ V _`. Take `⟨la, hla⟩` from `exists_place_le V`. Establish `hV : (la.valuation F).valuationSubring = V` using `ValuationSubring.eq_of_le_of_ne_top _ hla (ne_top_of_isDiscreteValuationRing V)`. Substitute `hV` using the available equality. Establish `hc : IsAdicComplete (maximalIdeal (la.adicCompletionIntegers F)) (la.adicCompletionIntegers F)`.

Use `NormIntegers.isAdicComplete_of_fg (C := la.adicCompletion F) ⟨?_, ?_, ?_⟩ (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top` and prove the remaining obligations. Conclude with `FaithfulSMul.algebraMap_injective _ _`. Introduce `x`. Establish `: ‖(x : la.adicCompletion F)‖ ≤ 1` using `Valued.toNormedField.norm_le_one_iff.2 x.2`. Conclude with `this` after adjusting the coercions.

Introduce `x hx`. Establish `: ‖x‖ ≤ 1` using `by exact_mod_cast hx`. Conclude with `⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩`. Set `φ : (la.valuation F).valuationSubring →+* la.adicCompletionIntegers F` to `((FinitePlace.embedding la).comp (la.valuation F).valuationSubring.subtype).codRestrict _ (fun x => by`. Rewrite using `[RingHom.comp_apply, mem_adicCompletionIntegers, ValuationSubring.coe_subtype, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']`.

Conclude with `(Valuation.mem_valuationSubring_iff _ _).1 x.2)`. Use `⟨la.adicCompletionIntegers F, inferInstance, inferInstance, inferInstance, hc, φ, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Conclude with `Subtype.ext ((FinitePlace.embedding la).injective (congrArg Subtype.val h))`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations.

Rewrite `ha` using `[adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Establish `h1 : la.valuation F (a : F) = 1`. Rewrite using `[← valuedAdicCompletion_eq_valuation']`. Conclude with `ha`. Conclude with `(Valuation.valuationSubring.integers (la.valuation F)).isUnit_iff_valuation_eq_one.2 h1`.
-/
theorem exists_complete : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V],
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O),
      Function.Injective φ ∧ IsLocalHom φ := by
  intro F _ _ V _
  obtain ⟨la, hla⟩ := exists_place_le V
  have hV : (la.valuation F).valuationSubring = V :=
    ValuationSubring.eq_of_le_of_ne_top _ hla (ne_top_of_isDiscreteValuationRing V)
  subst hV
  have hc : IsAdicComplete (maximalIdeal (la.adicCompletionIntegers F)) (la.adicCompletionIntegers F) := by
    refine NormIntegers.isAdicComplete_of_fg (C := la.adicCompletion F) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : la.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  let φ : (la.valuation F).valuationSubring →+* la.adicCompletionIntegers F :=
    ((FinitePlace.embedding la).comp (la.valuation F).valuationSubring.subtype).codRestrict _ (fun x => by
      rw [RingHom.comp_apply, mem_adicCompletionIntegers, ValuationSubring.coe_subtype,
        FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']
      exact (Valuation.mem_valuationSubring_iff _ _).1 x.2)
  refine ⟨la.adicCompletionIntegers F, inferInstance, inferInstance, inferInstance, hc, φ, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext ((FinitePlace.embedding la).injective (congrArg Subtype.val h))
  · refine ⟨fun a ha => ?_⟩
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one] at ha
    have h1 : la.valuation F (a : F) = 1 := by
      rw [← valuedAdicCompletion_eq_valuation']
      exact ha
    exact (Valuation.valuationSubring.integers (la.valuation F)).isUnit_iff_valuation_eq_one.2 h1

end GlobalTheory.CompleteDVR
