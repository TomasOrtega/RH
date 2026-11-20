import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

section
variable {E K K' : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K']

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem ringOfIntegers_hom_injective (τ : 𝓞 E →+* 𝓞 K) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  have : (RingHom.ker τ).IsPrime := RingHom.ker_isPrime τ
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem existsUnique_extend_ringOfIntegers_hom (τ : 𝓞 E →+* 𝓞 K) :
    ∃! τ' : E →+* K, ∀ a : 𝓞 E, τ' a = τ a := by
  have hi : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective).comp (ringOfIntegers_hom_injective τ)
  have hl : ∀ a : 𝓞 E, (IsFractionRing.lift hi : E →+* K) (algebraMap (𝓞 E) E a) = algebraMap (𝓞 K) K (τ a) :=
    fun a => IsFractionRing.lift_algebraMap (A := 𝓞 E) (K := E) hi a
  generalize (IsFractionRing.lift hi : E →+* K) = σ₀ at hl
  refine ⟨σ₀, hl, fun σ hσ => ?_⟩
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  exact (hσ a).trans (hl a).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem mapRingHom_bijective :
    Function.Bijective fun σ : E →+* K => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K) := by
  constructor
  · intro σ σ' h
    refine (existsUnique_extend_ringOfIntegers_hom (RingOfIntegers.mapRingHom σ)).unique (fun a => rfl) fun a => ?_
    have h' : RingOfIntegers.mapRingHom σ = RingOfIntegers.mapRingHom σ' := h
    rw [h']
    rfl
  · intro τ
    obtain ⟨σ, hσ⟩ := (existsUnique_extend_ringOfIntegers_hom τ).exists
    exact ⟨σ, RingHom.ext fun a => RingOfIntegers.ext (hσ a)⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem splits_iff_card : Splits E K ↔ Nat.card (E →+* K) = Module.finrank ℚ E := by
  rw [Splits, ← Nat.card_eq_of_bijective _ (mapRingHom_bijective (E := E) (K := K))]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_ringHom_le_finrank : Nat.card (E →+* K) ≤ Module.finrank ℚ E := by
  rw [Nat.card_congr (RingHom.equivRatAlgHom E K)]
  exact card_algHom_le_finrank ℚ E K

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem comp_bijective_of_splits (j : K →+* K') (h : Splits E K) :
    Function.Bijective fun σ : E →+* K => j.comp σ := by
  have : Finite (E →+* K') := Finite.of_equiv _ (RingHom.equivRatAlgHom E K').symm
  have hi : Function.Injective fun σ : E →+* K => j.comp σ := fun σ σ' e =>
    RingHom.ext fun a => j.injective (DFunLike.congr_fun e a)
  refine hi.bijective_of_nat_card_le ?_
  rw [splits_iff_card.1 h]
  exact card_ringHom_le_finrank

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem splits_basic : ∀ (E : Type) [Field E] [NumberField E], (∃ k : IntermediateField ℚ ℂ, FiniteDimensional ℚ k ∧ ∀ (τ : E →+* ℂ) a, τ a ∈ k) ∧ (∀ (k : IntermediateField ℚ ℂ) [NumberField k], (∀ (τ : E →+* ℂ) a, τ a ∈ k) → Splits E k) ∧ ∀ (K : Type) [Field K] [NumberField K], (Splits E K ↔ Nat.card (E →+* K) = Module.finrank ℚ E) ∧ (∀ τ : 𝓞 E →+* 𝓞 K, ∃! τ' : E →+* K, ∀ a : 𝓞 E, τ' a = τ a) ∧ ∀ (K' : Type) [Field K'] [NumberField K'] (j : K →+* K'), Splits E K → Splits E K' ∧ Function.Bijective fun τ : 𝓞 E →+* 𝓞 K => (RingOfIntegers.mapRingHom j).comp τ := by
  intro E _ _
  refine ⟨⟨IntermediateField.normalClosure ℚ E ℂ, inferInstance, fun τ a => ?_⟩, fun k _ hk => ?_,
    fun K _ _ => ⟨splits_iff_card, existsUnique_extend_ringOfIntegers_hom, fun K' _ _ j h => ⟨?_, ?_⟩⟩⟩
  · exact AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩
  · rw [splits_iff_card, ← Embeddings.card E ℂ, ← Nat.card_eq_fintype_card]
    refine Nat.card_eq_of_bijective (fun σ => (algebraMap k ℂ).comp σ) ⟨fun σ σ' e => ?_, fun τ => ?_⟩
    · exact RingHom.ext fun a => (algebraMap k ℂ).injective (DFunLike.congr_fun e a)
    · exact ⟨τ.codRestrict k (hk τ), RingHom.ext fun a => rfl⟩
  · rw [splits_iff_card, ← Nat.card_eq_of_bijective _ (comp_bijective_of_splits j h)]
    exact splits_iff_card.1 h
  · have e : ((fun τ : 𝓞 E →+* 𝓞 K => (RingOfIntegers.mapRingHom j).comp τ) ∘
        fun σ : E →+* K => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K)) =
        (fun σ : E →+* K' => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K')) ∘ fun σ : E →+* K => j.comp σ := by
      funext σ
      exact RingHom.ext fun a => rfl
    rw [← Function.Bijective.of_comp_iff _ (mapRingHom_bijective (E := E) (K := K)), e]
    exact mapRingHom_bijective.comp (comp_bijective_of_splits j h)

end GlobalTheory.CM
