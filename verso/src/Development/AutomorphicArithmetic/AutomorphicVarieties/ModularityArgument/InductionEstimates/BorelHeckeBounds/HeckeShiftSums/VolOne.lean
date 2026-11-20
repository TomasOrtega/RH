import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.TorusDifference

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

/- English proof (translation)
Introduce `K _ _ n r`. Establish `h1 : ∀ n r : ℕ, unipMeasure K n r (unipFundamentalDomain K n r) = 1` using `fun n r => by`. Rewrite using `[unipMeasure, unipFundamentalDomain, Measure.pi_pi]`. Simplify using `[GroundTheory.Global.adeleMeasure_fundamentalSet]`. Use `⟨h1 n r, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[volN, Measure.real, h1]`. Simplify using the standard rewrite rules. Take `⟨C, hC, hsub⟩` from `exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)`. Use `⟨C, hC, hsub, fun X => ?_⟩` and prove the remaining obligations. Use `choose k hk _ using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (X p)`.

Use `⟨⟨fun p => algebraMap K 𝔸[K] (-k p), fun p => -k p, rfl⟩, hsub ?_⟩` and prove the remaining obligations. Introduce `p _`. Express the relevant statement in the definitionally equal form `algebraMap K 𝔸[K] (-k p) + X p ∈ GroundTheory.Global.fundamentalSet K`. Rewrite using `[map_neg, neg_add_eq_sub]`. Conclude with `hk p`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.volOne :
    ∀ {K : Type} [Field K] [NumberField K] (n r : ℕ), unipMeasure K n r (unipFundamentalDomain K n r) = 1 ∧ volN K = 1 ∧
      ∃ C : Set (UPos n r → 𝔸[K]), IsCompact C ∧ unipFundamentalDomain K n r ⊆ C ∧ ∀ X : UPos n r → 𝔸[K], ∃ ξ : unipLattice K n r, ξ.1 + X ∈ C := by
  intro K _ _ n r
  have h1 : ∀ n r : ℕ, unipMeasure K n r (unipFundamentalDomain K n r) = 1 := fun n r => by
    rw [unipMeasure, unipFundamentalDomain, Measure.pi_pi]
    simp [GroundTheory.Global.adeleMeasure_fundamentalSet]
  refine ⟨h1 n r, ?_, ?_⟩
  · rw [volN, Measure.real, h1]; simp
  · obtain ⟨C, hC, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
    refine ⟨C, hC, hsub, fun X => ?_⟩
    choose k hk _ using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (X p)
    refine ⟨⟨fun p => algebraMap K 𝔸[K] (-k p), fun p => -k p, rfl⟩, hsub ?_⟩
    intro p _
    change algebraMap K 𝔸[K] (-k p) + X p ∈ GroundTheory.Global.fundamentalSet K
    rw [map_neg, neg_add_eq_sub]
    exact hk p
