import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _ β hβ g`. Take `⟨hm, hs⟩` from `hβ`. Use `haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)`. Set `e : F → AdeleRing.principalSubgroup (𝓞 F) F` to `fun ξ => ⟨rt ξ, ξ, rfl⟩`. Establish `he : Function.Bijective e`.

Prove the components needed by the constructor for the conclusion. Introduce `a b h`. Conclude with `AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)`. Introduce and unpack `⟨_, ξ, rfl⟩`. Conclude with `⟨ξ, rfl⟩`.

Use `haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := he.surjective.countable`. Establish `hfd` using `isAddFundamentalDomain_fundamentalSet F`. Establish `hf : Measurable fun b : A F => β (nU b * g)` using `hm.comp (M.continuous_nU.mul continuous_const).measurable`. Rewrite using `[hfd.lintegral_eq_tsum'' (fun b => β (nU b * g)), ← lintegral_tsum]`. Establish `hone : ∀ x : A F, ∑' k : AdeleRing.principalSubgroup (𝓞 F) F, β (nU (k +ᵥ x) * g) = 1`.

Introduce `x`. Rewrite using `[← (Equiv.ofBijective e he).tsum_eq, ← hs (nU x * g)]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `β (nU (rt ξ + x) * g) = _`. Rewrite using `[M.nU_add, mul_assoc]`.

Simplify using `only [hone, lintegral_const, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter, adeleMeasure_fundamentalSet, one_mul]`. Introduce `k`. Conclude with `(hf.comp (measurable_const_vadd k)).aemeasurable`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.wtOne :
    ∀ (F : Type) [Field F] [NumberField F] (β : G1 F → ℝ≥0∞), M.NWt β → ∀ g, ∫⁻ b, β (nU b * g) ∂(adeleMeasure F) = 1 := by
  intro F _ _ β hβ g
  obtain ⟨hm, hs⟩ := hβ
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let e : F → AdeleRing.principalSubgroup (𝓞 F) F := fun ξ => ⟨rt ξ, ξ, rfl⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b h
      exact AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)
    · rintro ⟨_, ξ, rfl⟩
      exact ⟨ξ, rfl⟩
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := he.surjective.countable
  have hfd := isAddFundamentalDomain_fundamentalSet F
  have hf : Measurable fun b : A F => β (nU b * g) :=
    hm.comp (M.continuous_nU.mul continuous_const).measurable
  rw [hfd.lintegral_eq_tsum'' (fun b => β (nU b * g)), ← lintegral_tsum]
  · have hone : ∀ x : A F,
        ∑' k : AdeleRing.principalSubgroup (𝓞 F) F, β (nU (k +ᵥ x) * g) = 1 := by
      intro x
      rw [← (Equiv.ofBijective e he).tsum_eq, ← hs (nU x * g)]
      refine tsum_congr fun ξ => ?_
      change β (nU (rt ξ + x) * g) = _
      rw [M.nU_add, mul_assoc]
    simp only [hone, lintegral_const, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter,
      adeleMeasure_fundamentalSet, one_mul]
  · intro k
    exact (hf.comp (measurable_const_vadd k)).aemeasurable
