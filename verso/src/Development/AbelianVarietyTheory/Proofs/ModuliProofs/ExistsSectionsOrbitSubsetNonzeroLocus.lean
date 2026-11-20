import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory

/- English proof (translation)
Establish `orbit : ∀ x : X, ∃ e : ℕ, 0 < e ∧ ∃ f ∈ ProjSpace.grading R N e, Set.range (fun g => φ g x) ⊆ Proj.basicOpen (ProjSpace.grading R N) f` using `fun x => FiniteSubsetsInAffineOpens.exists_proj_basicOpen (ProjSpace.grading R N) (Set.finite_range _)`. Use `choose e he f hf hsub using orbit`. Set `U : X → Set X` to `fun x => {z | ∀ g, φ g z ∈ Proj.basicOpen (ProjSpace.grading R N) (f x)}`. Establish `hU : ∀ x, U x ∈ nhds x` using `fun x => by`. Use `IsOpen.mem_nhds ?_ fun g => hsub x ⟨g, rfl⟩` and prove the remaining obligations.

Simplify using `only [U, Set.ofPred_forall]`. Conclude with `isOpen_iInter_of_finite fun g => (φ g).continuous.isOpen_preimage _ (Proj.basicOpen (ProjSpace.grading R N) (f x)).isOpen`. Take `⟨t, ht⟩` from `CompactSpace.elim_nhds_subcover U hU`. Establish `hD : 0 < ∏ x ∈ t, e x` using `Finset.prod_pos fun x _ => he x`. Establish `hdvd : ∀ x ∈ t, e x ∣ ∏ y ∈ t, e y` using `fun x hx => Finset.dvd_prod_of_mem e hx`.

Use `⟨∏ x ∈ t, e x, t.card, fun i => f (t.equivFin.symm i) ^ ((∏ x ∈ t, e x) / e (t.equivFin.symm i)), hD, fun i => ?_, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : (f (t.equivFin.symm i)).IsHomogeneous (e (t.equivFin.symm i))` using `hf _`. Establish `h2` using `h1.pow ((∏ x ∈ t, e x) / e (t.equivFin.symm i))`. Rewrite `h2` using `[Nat.mul_div_cancel' (hdvd _ (t.equivFin.symm i).2)]`. Then use the resulting hypothesis. Establish `hx : x ∈ ⋃ y ∈ t, U y` using `by rw [ht]; exact Set.mem_univ x`.

Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.1 hx`. Establish `hxy' : ∀ g, φ g x ∈ Proj.basicOpen (ProjSpace.grading R N) (f y)` using `hxy`. Use `⟨t.equivFin ⟨y, hy⟩, fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`. Rewrite using `[Proj.basicOpen_pow]`.

Conclude with `hxy' g`. Conclude with `Nat.div_pos (Nat.le_of_dvd hD (hdvd y hy)) (he y)`.
-/
theorem exists_forms_forall_mem_basicOpen {Γ : Type} [Finite Γ] {R : Type} [CommRing R] {N : ℕ}
    {X : Scheme.{0}} [CompactSpace X] (φ : Γ → (X ⟶ PSpace R N)) :
    ∃ (d n : ℕ) (F : Fin n → MvPolynomial (Fin (N + 1)) R), 0 < d ∧ (∀ i, (F i).IsHomogeneous d) ∧
      ∀ x : X, ∃ i, ∀ g, φ g x ∈ Proj.basicOpen (ProjSpace.grading R N) (F i) := by
  classical

  have orbit : ∀ x : X, ∃ e : ℕ, 0 < e ∧ ∃ f ∈ ProjSpace.grading R N e,
      Set.range (fun g => φ g x) ⊆ Proj.basicOpen (ProjSpace.grading R N) f := fun x =>
    FiniteSubsetsInAffineOpens.exists_proj_basicOpen (ProjSpace.grading R N) (Set.finite_range _)
  choose e he f hf hsub using orbit

  let U : X → Set X := fun x => {z | ∀ g, φ g z ∈ Proj.basicOpen (ProjSpace.grading R N) (f x)}
  have hU : ∀ x, U x ∈ nhds x := fun x => by
    refine IsOpen.mem_nhds ?_ fun g => hsub x ⟨g, rfl⟩
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun g =>
      (φ g).continuous.isOpen_preimage _ (Proj.basicOpen (ProjSpace.grading R N) (f x)).isOpen

  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU
  have hD : 0 < ∏ x ∈ t, e x := Finset.prod_pos fun x _ => he x
  have hdvd : ∀ x ∈ t, e x ∣ ∏ y ∈ t, e y := fun x hx => Finset.dvd_prod_of_mem e hx
  refine ⟨∏ x ∈ t, e x, t.card,
    fun i => f (t.equivFin.symm i) ^ ((∏ x ∈ t, e x) / e (t.equivFin.symm i)), hD, fun i => ?_, fun x => ?_⟩
  · have h1 : (f (t.equivFin.symm i)).IsHomogeneous (e (t.equivFin.symm i)) := hf _
    have h2 := h1.pow ((∏ x ∈ t, e x) / e (t.equivFin.symm i))
    rwa [Nat.mul_div_cancel' (hdvd _ (t.equivFin.symm i).2)] at h2
  · have hx : x ∈ ⋃ y ∈ t, U y := by rw [ht]; exact Set.mem_univ x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hx
    have hxy' : ∀ g, φ g x ∈ Proj.basicOpen (ProjSpace.grading R N) (f y) := hxy
    refine ⟨t.equivFin ⟨y, hy⟩, fun g => ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [Proj.basicOpen_pow]
    · exact hxy' g
    · exact Nat.div_pos (Nat.le_of_dvd hD (hdvd y hy)) (he y)

/- English proof (translation)
Introduce `Γ _ _ R _ X s ρ hs`. Take `⟨N, j, hj, -⟩` from `hs`. Use `haveI : CompactSpace (PSpace R N) := by`. Use `⟨?_⟩` and prove the remaining obligations. Establish `hcov : (Set.univ : Set (PSpace R N)) = ⋃ i, (ProjSpace.chart R N i : Set (PSpace R N))`.

Use extensionality with `y`. Simplify using `only [Set.mem_univ, Set.mem_iUnion, true_iff]`. Conclude with `ProjSpace.exists_mem_chart R N y`. Rewrite using `[hcov]`. Conclude with `isCompact_iUnion fun i => (ProjSpace.isAffineOpen_chart R N i).isCompact`.

Use `haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j`. Take `⟨d, n, F, hd, hF, hcov⟩` from `exists_forms_forall_mem_basicOpen (fun g => (ρ g).hom ≫ j)`. Use `⟨(lbPow (ProjSpace.O1 R N) d).pull j, n, fun i => secPull (ProjSpace.formSec d (F i) (hF i)) j, pull_isLB (isLB_lbPow (ProjSpace.O1_isLB R N) d) j, fun i => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]`. Conclude with `(Proj.isAffineOpen_basicOpen (ProjSpace.grading R N) (F i) (hF i) hd).preimage j`.

Take `⟨i, hi⟩` from `hcov x`. Use `⟨i, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]`. Conclude with `hi g`.
-/
theorem exists_sections_orbit_subset_nonzeroLocus : ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (ρ : Γ →* Aut X), IsProjOver s → ∃ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧ ∀ x : X, ∃ i, ∀ g, (ρ g).hom x ∈ Out.nonzeroLocus (σ i) := by
  intro Γ _ _ R _ X s ρ hs
  obtain ⟨N, j, hj, -⟩ := hs

  haveI : CompactSpace (PSpace R N) := by
    refine ⟨?_⟩
    have hcov : (Set.univ : Set (PSpace R N)) = ⋃ i, (ProjSpace.chart R N i : Set (PSpace R N)) := by
      ext y
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      exact ProjSpace.exists_mem_chart R N y
    rw [hcov]
    exact isCompact_iUnion fun i => (ProjSpace.isAffineOpen_chart R N i).isCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j

  obtain ⟨d, n, F, hd, hF, hcov⟩ := exists_forms_forall_mem_basicOpen (fun g => (ρ g).hom ≫ j)
  refine ⟨(lbPow (ProjSpace.O1 R N) d).pull j, n, fun i => secPull (ProjSpace.formSec d (F i) (hF i)) j,
    pull_isLB (isLB_lbPow (ProjSpace.O1_isLB R N) d) j, fun i => ?_, fun x => ?_⟩
  · rw [nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]
    exact (Proj.isAffineOpen_basicOpen (ProjSpace.grading R N) (F i) (hF i) hd).preimage j
  · obtain ⟨i, hi⟩ := hcov x
    refine ⟨i, fun g => ?_⟩
    rw [nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]
    exact hi g

end GlobalTheory
