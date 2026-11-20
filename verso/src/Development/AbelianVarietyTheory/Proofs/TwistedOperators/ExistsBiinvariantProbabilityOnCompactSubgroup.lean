import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ K hK`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Use `haveI : BorelSpace K := Subtype.borelSpace (K : Set G)`. Set `μ : Measure K` to `Measure.haarMeasure ⊤`. Use `haveI hμ : IsProbabilityMeasure μ := ⟨by`.

Use `Measure.haarMeasure_self (G := K) (K₀ := ⊤)` as an intermediate fact. Simplify using `using this⟩`. Use `haveI hH : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _`. Establish `hv : Measurable (Subtype.val : K → G)` using `measurable_subtype_coe`. Establish `hKm : MeasurableSet (K : Set G)` using `hK.isClosed.measurableSet`.

Use `⟨μ.map Subtype.val, Measure.isProbabilityMeasure_map hv.aemeasurable, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hv hKm.compl]`. Establish `: (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Introduce `k hk`. Rewrite using `[Measure.map_map (measurable_const_mul k) hv]`. Establish `h1 : μ.map (fun x : K => (⟨k, hk⟩ : K) * x) = μ` using `map_mul_left_eq_self μ _`.

Use `conv_rhs => rw [← h1]`. Rewrite using `[Measure.map_map hv (measurable_const_mul _)]`. Both sides reduce to the same expression. Introduce `k hk`. Rewrite using `[Measure.map_map (measurable_mul_const k) hv]`.

Establish `h1 : μ.map (fun x : K => x * (⟨k, hk⟩ : K)) = μ` using `by haveI : IsProbabilityMeasure (μ.map (fun x : K => x * (⟨k, hk⟩ : K))) := Measure.isProbabilityMeasure_map (measurable_mul_const _).aemeasurable haveI : (μ.map (fun x : K => x * (⟨k, hk⟩ : K))).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ _`. Conclude with `Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _`. Use `conv_rhs => rw [← h1]`. Rewrite using `[Measure.map_map hv (measurable_mul_const _)]`. Both sides reduce to the same expression.
-/
theorem exists_biinvariant_probability_on_compact_subgroup :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ mK : Measure G, IsProbabilityMeasure mK ∧ mK (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, Measure.map (fun x => k * x) mK = mK) ∧ ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK := by
  intro G _ _ _ _ _ _ _ K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : BorelSpace K := Subtype.borelSpace (K : Set G)
  let μ : Measure K := Measure.haarMeasure ⊤
  haveI hμ : IsProbabilityMeasure μ := ⟨by
    have := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    simpa using this⟩
  haveI hH : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hv : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hKm : MeasurableSet (K : Set G) := hK.isClosed.measurableSet
  refine ⟨μ.map Subtype.val, Measure.isProbabilityMeasure_map hv.aemeasurable, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hv hKm.compl]
    have : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x; simp
    rw [this]; simp
  · intro k hk
    rw [Measure.map_map (measurable_const_mul k) hv]
    have h1 : μ.map (fun x : K => (⟨k, hk⟩ : K) * x) = μ := map_mul_left_eq_self μ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_const_mul _)]
    rfl
  · intro k hk
    rw [Measure.map_map (measurable_mul_const k) hv]
    have h1 : μ.map (fun x : K => x * (⟨k, hk⟩ : K)) = μ := by
      haveI : IsProbabilityMeasure (μ.map (fun x : K => x * (⟨k, hk⟩ : K))) :=
        Measure.isProbabilityMeasure_map (measurable_mul_const _).aemeasurable
      haveI : (μ.map (fun x : K => x * (⟨k, hk⟩ : K))).IsHaarMeasure :=
        Measure.isHaarMeasure_map_mul_right μ _
      exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_mul_const _)]
    rfl

end GlobalTheory
