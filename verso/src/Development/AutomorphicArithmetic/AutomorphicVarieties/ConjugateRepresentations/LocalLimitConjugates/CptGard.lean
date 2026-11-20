import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OrbLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.DmTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OrbConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.IsOpenMapVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem summable_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {u v : G → ℂ} (hu : HasCompactSupport u)
    (hv : HasCompactSupport v) (x : G) : Summable fun γ : Γ => GlobalTheory.AutomorphicL2Unitary.conv μ u v (γ * x) := by
  obtain ⟨N, hN⟩ := (locInt G Γ μ).2 _ (IsCompact.mul hu hv)
  refine summable_of_hasFiniteSupport ((Set.finite_of_encard_le_coe (hN x)).subset fun γ hγ => ?_)
  by_contra hn
  refine hγ ?_
  have h0 : (fun y => u y * v (y⁻¹ * ((γ : G) * x))) = 0 := by
    funext y
    by_contra hy
    exact hn ⟨y, subset_tsupport u (left_ne_zero_of_mul hy), y⁻¹ * ((γ : G) * x),
      subset_tsupport v (right_ne_zero_of_mul hy), mul_inv_cancel_left _ _⟩
  simp only [GlobalTheory.AutomorphicL2Unitary.conv, h0]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.H.cptGard :
    UpperTheory.V.Cj.H.CptGard := by
  intro E _ _ _ a μ _ _ φ hl hi C hC hs
  obtain ⟨f, hf, hφ⟩ := orbLift E a φ hl hi C hC hs
  obtain ⟨k, u, v, huv, hsum⟩ := dmTest E a μ f hf
  have hc : ∀ ψ : Sm E a, IsTest ψ → Continuous ψ.1 := fun ψ h => ((testOps E a ψ).1 h.2).1
  choose h hh using fun i => orbConv (GA E a) (latticeGL E a) μ (u i).1 (v i).1 (hc _ (huv i).1) (huv i).1.1
    (hc _ (huv i).2) (huv i).2.1
  have e : φ = ∑ i, (⟨cv (v i).1 (h i).toL2, cvSm E a μ (v i) (huv i).2 _⟩ : Sm E a) := by
    apply Subtype.ext
    rw [hφ, hsum, Submodule.coe_sum]
    funext x
    simp only [Finset.sum_apply, ← hh, GlobalTheory.AutomorphicL2Unitary.orbitSum]
    exact Summable.tsum_finsetSum fun i _ => summable_conv _ μ (huv i).1.1 (huv i).2.1 x
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨v i, (h i).toL2, (huv i).2, rfl⟩
