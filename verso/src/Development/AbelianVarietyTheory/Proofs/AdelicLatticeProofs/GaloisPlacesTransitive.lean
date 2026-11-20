import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct Pointwise

namespace GlobalTheory.CNorm

/- English proof (translation)
Introduce `F E _ _ _ _ _ _`. Use `⟨fun σ w => ?_, fun w w' hu => ?_⟩` and prove the remaining obligations. Use `set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ.toRingEquiv with he`. Establish `hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = σ (x : E)` using `fun x => rfl`. Establish `hfix : ∀ a : 𝓞 F, e (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a`.

Introduce `a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hc]`. Conclude with `σ.commutes (a : F)`. Use `⟨w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective, ?_, ?_⟩` and prove the remaining obligations.

Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `e (algebraMap (𝓞 F) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ w.asIdeal`. Rewrite using `[hfix]`. Introduce `y`.

Conclude with `valuation_of_eq_comap σ.toRingEquiv w _ rfl y`. Use `haveI := w.isPrime haveI := w'.isPrime haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩ haveI : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := hu ▸ ⟨rfl⟩`. Take `⟨σ, hσ⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal w'.asIdeal w.asIdeal (E ≃ₐ[F] E)`. Use `⟨σ, fun y => valuation_of_eq_comap σ.toRingEquiv w w' ?_ y⟩` and prove the remaining obligations. Use extensionality with `x`.

Rewrite using `[Ideal.mem_comap, ← hσ]`. Express the relevant statement in the definitionally equal form `_ ↔ σ • x ∈ _`. Conclude with `Ideal.smul_mem_pointwise_smul_iff.symm`.
-/
theorem galois_places_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], (∀ (τ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), ∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) ∧ ∀ y : E, w'.valuation E y = w.valuation E (τ y)) ∧ ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) → ∃ τ : E ≃ₐ[F] E, ∀ y : E, w'.valuation E y = w.valuation E (τ y) := by
  intro F E _ _ _ _ _ _
  refine ⟨fun σ w => ?_, fun w w' hu => ?_⟩
  · set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ.toRingEquiv with he
    have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = σ (x : E) := fun x => rfl
    have hfix : ∀ a : 𝓞 F, e (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
      intro a
      apply RingOfIntegers.ext
      rw [hc]
      exact σ.commutes (a : F)
    refine ⟨w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective, ?_, ?_⟩
    · apply HeightOneSpectrum.ext
      ext a
      change e (algebraMap (𝓞 F) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ w.asIdeal
      rw [hfix]
    · intro y
      exact valuation_of_eq_comap σ.toRingEquiv w _ rfl y
  · haveI := w.isPrime
    haveI := w'.isPrime
    haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    haveI : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := hu ▸ ⟨rfl⟩
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal
      w'.asIdeal w.asIdeal (E ≃ₐ[F] E)
    refine ⟨σ, fun y => valuation_of_eq_comap σ.toRingEquiv w w' ?_ y⟩
    ext x
    rw [Ideal.mem_comap, ← hσ]
    change _ ↔ σ • x ∈ _
    exact Ideal.smul_mem_pointwise_smul_iff.symm

end GlobalTheory.CNorm
