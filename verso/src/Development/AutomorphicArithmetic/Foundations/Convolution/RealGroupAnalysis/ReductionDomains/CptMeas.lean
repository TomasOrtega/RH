import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import GroundTheory.AutomorphicForms.RealIwasawaIntegration

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ K hK`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Establish `hKm : MeasurableSet (K : Set G)` using `hK.isClosed.measurableSet`. Establish `hval : Measurable (Subtype.val : K → G)` using `measurable_subtype_coe`. Set `μ : Measure K` to `Measure.haarMeasure ⊤`.

Use `haveI hH : μ.IsHaarMeasure := inferInstance`. Establish `hprob : IsProbabilityMeasure μ`. Use `⟨?_⟩` and prove the remaining obligations. Use `Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))` as an intermediate fact. Simplify using `using this`.

Use `haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)`. Use `haveI : μ.IsMulRightInvariant := GroundTheory.Automorphic.isMulRightInvariant_of_compactSpace μ`. Use `⟨μ, hH, hprob, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hval hKm.compl]`. Establish `: (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Simplify using `[this]`. Introduce `k hk`. Establish `hcomp : (fun x : G => k * x) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => (⟨k, hk⟩ : K) * x)`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[Measure.map_map (measurable_const_mul k) hval, hcomp, ← Measure.map_map hval (measurable_const_mul _), map_mul_left_eq_self]`. Introduce `k hk`. Establish `hcomp : (fun x : G => x * k) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => x * (⟨k, hk⟩ : K))`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[Measure.map_map (measurable_mul_const k) hval, hcomp, ← Measure.map_map hval (measurable_mul_const _), map_mul_right_eq_self]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.cptMeas :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ μK : Measure K, μK.IsHaarMeasure ∧ IsProbabilityMeasure μK ∧ (μK.map Subtype.val) (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, (μK.map Subtype.val).map (k * ·) = μK.map Subtype.val) ∧ ∀ k ∈ K, (μK.map Subtype.val).map (· * k) = μK.map Subtype.val := by
  intro G _ _ _ _ _ _ _ _ K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKm : MeasurableSet (K : Set G) := hK.isClosed.measurableSet
  have hval : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  let μ : Measure K := Measure.haarMeasure ⊤
  haveI hH : μ.IsHaarMeasure := inferInstance
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
    simpa using this
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  haveI : μ.IsMulRightInvariant := GroundTheory.Automorphic.isMulRightInvariant_of_compactSpace μ
  refine ⟨μ, hH, hprob, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hval hKm.compl]
    have : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x; simp
    simp [this]
  · intro k hk
    have hcomp : (fun x : G => k * x) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => (⟨k, hk⟩ : K) * x) := by
      ext x; simp
    rw [Measure.map_map (measurable_const_mul k) hval, hcomp,
      ← Measure.map_map hval (measurable_const_mul _), map_mul_left_eq_self]
  · intro k hk
    have hcomp : (fun x : G => x * k) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => x * (⟨k, hk⟩ : K)) := by
      ext x; simp
    rw [Measure.map_map (measurable_mul_const k) hval, hcomp,
      ← Measure.map_map hval (measurable_mul_const _), map_mul_right_eq_self]
