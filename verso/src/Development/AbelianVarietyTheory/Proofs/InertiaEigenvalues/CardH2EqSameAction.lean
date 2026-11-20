import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.H2CardScalars

/- English proof (translation)
Establish `hZ : ∀ f : G × G → M, f ∈ Z2 rho ↔ f ∈ Z2 rho'`. Introduce `f`. Rewrite using `[mem_cocycles2, mem_cocycles2]`. Simplify using `only [h]`. Establish `hd : ∀ c : G → M, d1 rho c = d1 rho' c` using `fun c => funext fun p => by`.

Simplify using `only [d1, LinearMap.coe_mk, AddHom.coe_mk, h]`. Establish `hB : ∀ f : G × G → M, f ∈ B2 rho ↔ f ∈ B2 rho'`. Introduce `f`. Rewrite using `[separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]`. Simplify using `only [hd]`.

Set `e : Z2 rho ≃ Z2 rho'` to `Equiv.subtypeEquiv (Equiv.refl _) hZ`. Apply `Nat.card_congr` to reduce the goal to its premises. Use `Quotient.congr e ?_` and prove the remaining obligations. Introduce `a b`. Rewrite using `[Submodule.quotientRel_def, Submodule.quotientRel_def]`.

Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub]`. Conclude with `hB _`.
-/
theorem card_H2_eq_of_same_action {R S : Type} [CommRing R] [CommRing S] {G : Type} [Group G]
    [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module R M] [Module S M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [ContinuousConstSMul S M]
    (rho : Representation R G M) (rho' : Representation S G M)
    (h : ∀ g m, rho g m = rho' g m) : Nat.card (H2 rho) = Nat.card (H2 rho') := by
  have hZ : ∀ f : G × G → M, f ∈ Z2 rho ↔ f ∈ Z2 rho' := by
    intro f; rw [mem_cocycles2, mem_cocycles2]; simp only [h]
  have hd : ∀ c : G → M, d1 rho c = d1 rho' c := fun c => funext fun p => by
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, h]
  have hB : ∀ f : G × G → M, f ∈ B2 rho ↔ f ∈ B2 rho' := by
    intro f; rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]; simp only [hd]
  let e : Z2 rho ≃ Z2 rho' := Equiv.subtypeEquiv (Equiv.refl _) hZ
  apply Nat.card_congr
  refine Quotient.congr e ?_
  intro a b
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub]
  exact hB _

end GlobalTheory.H2CardScalars
