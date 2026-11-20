import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModule
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {I : Type} {H : I → Type} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
  (φ : ∀ i, H i →* G) (hφ : ∀ i, Continuous (φ i)) (A : Type) [AddCommGroup A]

/- English proof (translation)
Take `⟨z, rfl⟩` from `cohomologyπ_surjective (divFunRep φ A) n x`. Use `set c := cochainOf (divFunRep φ A) (cocycleι (divFunRep φ A) n z) with hc`. Establish `hfin : (Set.range c).Finite` using `(isLocallyConstant_cochainOf _).range_finite`. Establish `hT : (⋃ f ∈ Set.range c, {i | ((f : divFun φ A) : I → G → A) i ≠ 0}).Finite` using `hfin.biUnion fun f _ => (f : divFun φ A).2.1`. Use `hT.subset fun i hi => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hiT`. Apply `hi` to reduce the goal to its premises. Establish `hz : cocyclesMapAlong (φ i) (hφ i) (divFunEval φ A i) n z = 0`. Apply `cocycleι_injective` to reduce the goal to its premises. Apply `cochainOf_injective` to reduce the goal to its premises.

Rewrite using `[cochainOf_cocycleι_cocyclesMapAlong, map_zero]`. Use function extensionality and compare the values at `h`. Rewrite using `[divFunEval_hom_apply]`. Establish `hmem : ((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `hiT (Set.mem_biUnion ⟨_, rfl⟩ hne)`. Express the relevant statement in the definitionally equal form `((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i 1 = 0`. Rewrite using `[hmem]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(cohomologyMapAlong (φ i) (hφ i) (divFunEval φ A i) n) (cohomologyπ (divFunRep φ A) n z) = 0`.

Rewrite using `[cohomologyMapAlong_cohomologyπ, hz, map_zero]`.
-/
theorem finite_divFunEval_ne_zero (n : ℕ) (x : cohomology (divFunRep φ A) n) :
    {i | (cohomologyMapAlong (φ i) (hφ i) (divFunEval φ A i) n).hom x ≠ 0}.Finite := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective (divFunRep φ A) n x
  set c := cochainOf (divFunRep φ A) (cocycleι (divFunRep φ A) n z) with hc
  have hfin : (Set.range c).Finite := (isLocallyConstant_cochainOf _).range_finite
  have hT : (⋃ f ∈ Set.range c, {i | ((f : divFun φ A) : I → G → A) i ≠ 0}).Finite :=
    hfin.biUnion fun f _ => (f : divFun φ A).2.1
  refine hT.subset fun i hi => ?_
  by_contra hiT
  apply hi
  have hz : cocyclesMapAlong (φ i) (hφ i) (divFunEval φ A i) n z = 0 := by
    apply cocycleι_injective
    apply cochainOf_injective
    rw [cochainOf_cocycleι_cocyclesMapAlong, map_zero]
    funext h
    rw [divFunEval_hom_apply]
    have hmem : ((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i = 0 := by
      by_contra hne
      exact hiT (Set.mem_biUnion ⟨_, rfl⟩ hne)
    change ((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i 1 = 0
    rw [hmem]
    rfl
  change (cohomologyMapAlong (φ i) (hφ i) (divFunEval φ A i) n) (cohomologyπ (divFunRep φ A) n z) = 0
  rw [cohomologyMapAlong_cohomologyπ, hz, map_zero]

end

end GroundTheory.ProfCoh
