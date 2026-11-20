import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyMemFixed

noncomputable section

open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.LFun Formalism.L2.Host PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.StrongMultOne

/- English proof (translation)
Introduce `g1 E _ _ _ a π hN φ hφ x hx`. Establish `hex : ∀ v : π.V, ∃ y : XB E a, (y : GA E a → ℂ) = v.1.1` using `fun v => (g1 E a π hN v.1 v.2).imp fun _ h => h.1`. Use `choose f hf using hex`. Set `ι : π.V →ₗ[ℂ] XB E a` to `{ toFun := f map_add' := fun u v => by`. Use `DFunLike.coe_injective ?_` and prove the remaining obligations.

Rewrite using `[BoundedContinuousFunction.coe_add, hf, hf, hf]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun c v => by`. Use `DFunLike.coe_injective ?_` and prove the remaining obligations. Use function extensionality and compare the values at `g`.

Rewrite using `[hf]`. Express the relevant statement in the definitionally equal form `_ = c • f v g`. Rewrite using `[congrFun (hf v) g]`. Use `rfl }`. Establish `hι : ∀ v, (ι v : GA E a → ℂ) = v.1.1` using `hf`.

Use `filter_upwards [AeFix.eventually_mem_fixed E a π ⟨φ, hφ⟩] with w hw B hB`. Distinguish the cases in `h0 : x = 0`. Conclude with `Or.inl h0`. Use `Or.inr ?_` and prove the remaining obligations. Establish `hxι : ι ⟨φ, hφ⟩ = x` using `DFunLike.coe_injective ((hι _).trans hx.symm)`.

Establish `hne : (⟨φ, hφ⟩ : π.V) ≠ 0` using `fun e => h0 (by rw [← hxι, e, map_zero])`. Establish `hsat : IsSatVecGL w (π.locRep w) ⟨φ, hφ⟩ B` using `hB.2 _ hw hne`. Establish `hint : ∀ g y, ι (π.locRep w g y) = repW a w g (ι y)` using `fun g y => by`. Use `DFunLike.coe_injective ?_` and prove the remaining obligations. Use function extensionality and compare the values at `h`.

Rewrite using `[hι]`. Express the relevant statement in the definitionally equal form `_ = (ι y) (h * fl a w g)`. Use `congrFun (hι y) (h * fl a w g)` as an intermediate fact. Rewrite using `[this]`. Both sides reduce to the same expression.

Use `hsat.map ι hint (by rw [hxι]; exact h0)` as an intermediate fact. Rewrite `this` using `[hxι]`. Then use the resulting hypothesis.
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
