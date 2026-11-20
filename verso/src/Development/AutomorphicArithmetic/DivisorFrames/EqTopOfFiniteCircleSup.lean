import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.ClosedSubgroupEqTopOfDense
import Development.AutomorphicArithmetic.DivisorFrames.EqTopOfCircleSup
open Filter Topology

/- English proof (translation)
Introduce `G _ _ _ M hM hμ ι s c hc`. Proceed by induction on `s using Finset.induction_on generalizing M with`. Consider the case `empty`. Introduce `h`. Use `UpperTheory.closed_subgroup_eq_top_of_dense G M hM hμ ?_` and prove the remaining obligations.

Simplify using `using h`. Consider the case `insert a s ha ih`. Introduce `h`. Use `UpperTheory.eq_top_of_circle_sup G M hM hμ (c a) (hc a) ?_` and prove the remaining obligations. Establish `hcl : IsClosed ((M ⊔ (c a).range : Subgroup G) : Set G)`.

Rewrite using `[Subgroup.mul_normal]`. Use `hM.mul_right_of_isCompact ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.coe_range]`. Conclude with `isCompact_range (hc a)`. Use `ih (M ⊔ (c a).range) hcl ?_ ?_` and prove the remaining obligations.

Introduce `μ hμc hk`. Conclude with `hμ μ hμc fun m hm => hk m (Subgroup.mem_sup_left hm)`. Rewrite `h` using `[Finset.iSup_insert, ← sup_assoc]`. Conclude with `h`.
-/
theorem UpperTheory.eq_top_of_finite_circle_sup :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Subgroup G), IsClosed (M : Set G) →
        (∀ μ : G →* Circle, Continuous μ → (∀ m ∈ M, μ m = 1) → μ = 1) →
        ∀ (ι : Type) (s : Finset ι) (c : ι → (Circle →* G)), (∀ i, Continuous (c i)) →
        (∀ W ∈ nhds (1 : G), ∃ O : OpenSubgroup G, ∀ o ∈ O, ∃ m ∈ M ⊔ ⨆ i ∈ s, (c i).range, ∃ w ∈ W, o = m * w) → M = ⊤ := by
  intro G _ _ _ M hM hμ ι s c hc
  classical
  induction s using Finset.induction_on generalizing M with
  | empty =>
    intro h
    refine UpperTheory.closed_subgroup_eq_top_of_dense G M hM hμ ?_
    simpa using h
  | insert a s ha ih =>
    intro h
    refine UpperTheory.eq_top_of_circle_sup G M hM hμ (c a) (hc a) ?_
    have hcl : IsClosed ((M ⊔ (c a).range : Subgroup G) : Set G) := by
      rw [Subgroup.mul_normal]
      refine hM.mul_right_of_isCompact ?_
      rw [MonoidHom.coe_range]
      exact isCompact_range (hc a)
    refine ih (M ⊔ (c a).range) hcl ?_ ?_
    · intro μ hμc hk
      exact hμ μ hμc fun m hm => hk m (Subgroup.mem_sup_left hm)
    · rw [Finset.iSup_insert, ← sup_assoc] at h
      exact h
