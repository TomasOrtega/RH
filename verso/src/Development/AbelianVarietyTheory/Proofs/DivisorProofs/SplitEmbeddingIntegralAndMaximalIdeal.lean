import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

/- English proof (translation)
Use `set O := v.adicCompletionIntegers F`. Establish `hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers O`. Use `Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)` as an intermediate fact. Conclude with `this`. Establish `ha : ∀ a : 𝓞 E, Valued.v (τ a) ≤ 1`.

Introduce `a`. Establish `h1 : IsIntegral ℤ (τ a)` using `IsIntegral.map τ (NumberField.RingOfIntegers.isIntegral_coe a)`. Establish `h2 : IsIntegral O (τ a)` using `h1.tower_top`. Conclude with `hv.mem_of_integral h2`. Use `⟨ha, ?_⟩` and prove the remaining obligations.

Set `φ : 𝓞 E →+* O` to `((τ : E →+* v.adicCompletion F).comp (algebraMap (𝓞 E) E)).codRestrict O.toSubring (fun a => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (ha a))`. Establish `hmem : ∀ a : 𝓞 E, a ∈ (IsLocalRing.maximalIdeal O).comap φ ↔ Valued.v (τ a) < 1`. Introduce `a`. Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]`. Express the relevant statement in the definitionally equal form `¬ Valued.v (τ a) = 1 ↔ _`.

Conclude with `⟨fun h => lt_of_le_of_ne (ha a) h, fun h => ne_of_lt h⟩`. Use `⟨(IsLocalRing.maximalIdeal O).comap φ, ?_, hmem⟩` and prove the remaining obligations. Apply `Ideal.IsPrime.isMaximal inferInstance` to reduce the goal to its premises. Introduce `hbot`. Take `⟨π, hπ, hπ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`.

Establish `hlt : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1`. Use `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v π).2 hπ` as an intermediate fact. Rewrite `this` using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation]`. Conclude with `this`. Establish `hne : (algebraMap (𝓞 F) (𝓞 E) π) ≠ 0`.

Introduce `h`. Apply `hπ0` to reduce the goal to its premises. Apply `FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)` to reduce the goal to its premises. Simplify using `using h`. Apply `hne` to reduce the goal to its premises.

Establish `: algebraMap (𝓞 F) (𝓞 E) π ∈ (IsLocalRing.maximalIdeal O).comap φ`. Rewrite using `[hmem]`. Establish `e : ((algebraMap (𝓞 F) (𝓞 E) π : 𝓞 E) : E) = algebraMap F E (π : F)`. Conclude with `(IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E π).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E π)`. Rewrite using `[e, AlgHom.commutes]`.

Conclude with `hlt`. Rewrite `this` using `[hbot]`. Simplify using `using this`.
-/
theorem GlobalTheory.adicEmbedding_integral_place (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) :
    (∀ a : 𝓞 E, Valued.v (τ a) ≤ 1) ∧ ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ ∀ a : 𝓞 E, a ∈ Q ↔ Valued.v (τ a) < 1 := by
  set O := v.adicCompletionIntegers F
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers O := by
    have := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)
    exact this
  have ha : ∀ a : 𝓞 E, Valued.v (τ a) ≤ 1 := by
    intro a
    have h1 : IsIntegral ℤ (τ a) := IsIntegral.map τ (NumberField.RingOfIntegers.isIntegral_coe a)
    have h2 : IsIntegral O (τ a) := h1.tower_top
    exact hv.mem_of_integral h2
  refine ⟨ha, ?_⟩
  let φ : 𝓞 E →+* O :=
    ((τ : E →+* v.adicCompletion F).comp (algebraMap (𝓞 E) E)).codRestrict O.toSubring
      (fun a => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (ha a))
  have hmem : ∀ a : 𝓞 E, a ∈ (IsLocalRing.maximalIdeal O).comap φ ↔ Valued.v (τ a) < 1 := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
    change ¬ Valued.v (τ a) = 1 ↔ _
    exact ⟨fun h => lt_of_le_of_ne (ha a) h, fun h => ne_of_lt h⟩
  refine ⟨(IsLocalRing.maximalIdeal O).comap φ, ?_, hmem⟩
  apply Ideal.IsPrime.isMaximal inferInstance
  intro hbot
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hlt : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v π).2 hπ
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at this
    exact this
  have hne : (algebraMap (𝓞 F) (𝓞 E) π) ≠ 0 := by
    intro h
    apply hπ0
    apply FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    simpa using h
  apply hne
  have : algebraMap (𝓞 F) (𝓞 E) π ∈ (IsLocalRing.maximalIdeal O).comap φ := by
    rw [hmem]
    have e : ((algebraMap (𝓞 F) (𝓞 E) π : 𝓞 E) : E) = algebraMap F E (π : F) := by
      exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E π).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E π)
    rw [e, AlgHom.commutes]
    exact hlt
  rw [hbot] at this
  simpa using this
