import Mathlib
import GroundTheory.ProfiniteCohomology.OpenNormal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/- English proof (translation)
Set `O : OpenNormalSubgroup G → Set (ι → G)` to `fun U => {y | ∀ y' : ι → G, (∀ i, (y i)⁻¹ * y' i ∈ U) → f y' = f y}`. Establish `hO : ∀ U, IsOpen (O U)`. Introduce `U`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `y hy`.

Establish `hopen : IsOpen ((fun w : ι → G => fun i => (y i)⁻¹ * w i) ⁻¹' Set.univ.pi fun _ => (U : Set G))` using `(isOpen_set_pi Set.finite_univ fun _ _ => U.toOpenSubgroup.isOpen).preimage (continuous_pi fun i => continuous_const.mul (continuous_apply i))`. Use `mem_of_superset (hopen.mem_nhds fun i _ => by simp) ?_` and prove the remaining obligations. Introduce `w hw y' hy'`. Establish `hw' : ∀ i, (y i)⁻¹ * w i ∈ U` using `fun i => hw i (Set.mem_univ i)`. Establish `h1 : f y' = f y` using `hy y' fun i => by`.

Use `mul_mem (hw' i) (hy' i)` as an intermediate fact. Rewrite `this` using `[mul_assoc, mul_inv_cancel_left]`. Then use the resulting hypothesis. Rewrite using `[h1, hy w hw']`. Establish `hcover : Set.univ ⊆ ⋃ U, O U`. Introduce `x _`.

Establish `hS : (fun w : ι → G => fun i => x i * w i) ⁻¹' (f ⁻¹' {f x}) ∈ 𝓝 (1 : ι → G)` using `((hf.isOpen_fiber (f x)).preimage (continuous_pi fun i => continuous_const.mul (continuous_apply i))).mem_nhds (by simp)`. Take `⟨U, -, hU⟩` from `(OpenNormalSubgroup.hasBasis_nhds_one_pi ι).mem_iff.mp hS`. Use `Set.mem_iUnion.mpr ⟨U, fun y' hy' => ?_⟩` and prove the remaining obligations. Use `hU (show (fun i => (x i)⁻¹ * y' i) ∈ Set.univ.pi fun _ => (U : Set G) from fun i _ => hy' i)` as an intermediate fact. Simplify using `using this`.

Establish `hdir : Directed (· ⊆ ·) O` using `fun U V => ⟨U ⊓ V, fun y hy y' hy' => hy y' fun i => (hy' i).1, fun y hy y' hy' => hy y' fun i => (hy' i).2⟩`. Take `⟨U, hU⟩` from `isCompact_univ.elim_directed_cover O hO hcover hdir`. Conclude with `⟨U, fun x y hxy => (hU (Set.mem_univ x) y hxy).symm⟩`.
-/
theorem exists_openNormalSubgroup_pi_of_isLocallyConstant {ι X : Type*} [Finite ι]
    {f : (ι → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : ι → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y := by

  let O : OpenNormalSubgroup G → Set (ι → G) := fun U =>
    {y | ∀ y' : ι → G, (∀ i, (y i)⁻¹ * y' i ∈ U) → f y' = f y}
  have hO : ∀ U, IsOpen (O U) := by
    intro U
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hopen : IsOpen ((fun w : ι → G => fun i => (y i)⁻¹ * w i) ⁻¹'
        Set.univ.pi fun _ => (U : Set G)) :=
      (isOpen_set_pi Set.finite_univ fun _ _ => U.toOpenSubgroup.isOpen).preimage
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))
    refine mem_of_superset (hopen.mem_nhds fun i _ => by simp) ?_
    intro w hw y' hy'
    have hw' : ∀ i, (y i)⁻¹ * w i ∈ U := fun i => hw i (Set.mem_univ i)
    have h1 : f y' = f y := hy y' fun i => by
      have := mul_mem (hw' i) (hy' i)
      rwa [mul_assoc, mul_inv_cancel_left] at this
    rw [h1, hy w hw']
  have hcover : Set.univ ⊆ ⋃ U, O U := by
    intro x _
    have hS : (fun w : ι → G => fun i => x i * w i) ⁻¹' (f ⁻¹' {f x}) ∈ 𝓝 (1 : ι → G) :=
      ((hf.isOpen_fiber (f x)).preimage
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))).mem_nhds
        (by simp)
    obtain ⟨U, -, hU⟩ := (OpenNormalSubgroup.hasBasis_nhds_one_pi ι).mem_iff.mp hS
    refine Set.mem_iUnion.mpr ⟨U, fun y' hy' => ?_⟩
    have := hU (show (fun i => (x i)⁻¹ * y' i) ∈ Set.univ.pi fun _ => (U : Set G) from
      fun i _ => hy' i)
    simpa using this
  have hdir : Directed (· ⊆ ·) O := fun U V =>
    ⟨U ⊓ V, fun y hy y' hy' => hy y' fun i => (hy' i).1,
      fun y hy y' hy' => hy y' fun i => (hy' i).2⟩
  obtain ⟨U, hU⟩ := isCompact_univ.elim_directed_cover O hO hcover hdir
  exact ⟨U, fun x y hxy => (hU (Set.mem_univ x) y hxy).symm⟩

/- English proof (translation)
Take `⟨U, hU⟩` from `exists_openNormalSubgroup_pi_of_isLocallyConstant hf`. Use `⟨U, fun q => f fun i => (q i).out, funext fun x => hU _ _ fun i => ?_⟩` and prove the remaining obligations. Conclude with `QuotientGroup.eq.mp (QuotientGroup.out_eq' (x i : G ⧸ (U : Subgroup G))).symm`.
-/
theorem exists_openNormalSubgroup_factor_of_isLocallyConstant {ι X : Type*} [Finite ι]
    {f : (ι → G) → X} (hf : IsLocallyConstant f) :
    ∃ (U : OpenNormalSubgroup G) (g : (ι → G ⧸ (U : Subgroup G)) → X),
      f = g ∘ fun x i => (x i : G ⧸ (U : Subgroup G)) := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_pi_of_isLocallyConstant hf
  refine ⟨U, fun q => f fun i => (q i).out, funext fun x => hU _ _ fun i => ?_⟩
  exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (x i : G ⧸ (U : Subgroup G))).symm

/- English proof (translation)
The claim follows from `exists_openNormalSubgroup_pi_of_isLocallyConstant hf`.
-/
theorem exists_openNormalSubgroup_fin_of_isLocallyConstant {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : Fin n → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y :=
  exists_openNormalSubgroup_pi_of_isLocallyConstant hf

/- English proof (translation)
The claim follows from `exists_openNormalSubgroup_factor_of_isLocallyConstant hf`.
-/
theorem exists_openNormalSubgroup_factor_fin_of_isLocallyConstant {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ (U : OpenNormalSubgroup G) (g : (Fin n → G ⧸ (U : Subgroup G)) → X),
      f = g ∘ fun x i => (x i : G ⧸ (U : Subgroup G)) :=
  exists_openNormalSubgroup_factor_of_isLocallyConstant hf

end GroundTheory.ProfCoh
