import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyMemFixed

noncomputable section

open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.LFun Formalism.L2.Host PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.StrongMultOne

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Prove the first alternative.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem spherical_almost_everywhere_of_bounded : G1 → AlmostEverywhereSpherical := by
  intro g1 E _ _ _ a π hN φ hφ x hx
  have hex : ∀ v : π.V, ∃ y : XB E a, (y : GA E a → ℂ) = v.1.1 := fun v =>
    (g1 E a π hN v.1 v.2).imp fun _ h => h.1
  choose f hf using hex
  let ι : π.V →ₗ[ℂ] XB E a :=
    { toFun := f
      map_add' := fun u v => by
        refine DFunLike.coe_injective ?_
        rw [BoundedContinuousFunction.coe_add, hf, hf, hf]
        rfl
      map_smul' := fun c v => by
        refine DFunLike.coe_injective ?_
        funext g
        rw [hf]
        change _ = c • f v g
        rw [congrFun (hf v) g]
        rfl }
  have hι : ∀ v, (ι v : GA E a → ℂ) = v.1.1 := hf
  filter_upwards [AeFix.eventually_mem_fixed E a π ⟨φ, hφ⟩] with w hw B hB
  by_cases h0 : x = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have hxι : ι ⟨φ, hφ⟩ = x := DFunLike.coe_injective ((hι _).trans hx.symm)
  have hne : (⟨φ, hφ⟩ : π.V) ≠ 0 := fun e => h0 (by rw [← hxι, e, map_zero])
  have hsat : IsSatVecGL w (π.locRep w) ⟨φ, hφ⟩ B := hB.2 _ hw hne
  have hint : ∀ g y, ι (π.locRep w g y) = repW a w g (ι y) := fun g y => by
    refine DFunLike.coe_injective ?_
    funext h
    rw [hι]
    change _ = (ι y) (h * fl a w g)
    have := congrFun (hι y) (h * fl a w g)
    rw [this]
    rfl
  have := hsat.map ι hint (by rw [hxι]; exact h0)
  rwa [hxι] at this

end GlobalTheory.CompanionTheory.StrongMultOne

end
