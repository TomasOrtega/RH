import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
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
