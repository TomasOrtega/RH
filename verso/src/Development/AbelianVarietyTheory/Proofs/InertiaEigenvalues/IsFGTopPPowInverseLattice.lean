import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

/- English proof (translation)
Apply `IsTopologicalAddGroup.t2Space_of_zero_sep` to reduce the goal to its premises. Introduce `x hx`. Use `set ι := algebraMap O (FractionRing O)`. Establish `hsub : (ι ⁻¹' {x}).Subsingleton` using `fun a ha b hb => he.injective (ha.trans hb.symm)`. Establish `hcl : IsClosed (ι ⁻¹' {x})` using `hsub.isClosed`.

Use `⟨ι '' (ι ⁻¹' {x})ᶜ, ?_, ?_⟩` and prove the remaining obligations. Use `(he.isOpenMap _ hcl.isOpen_compl).mem_nhds ⟨0, ?_, map_zero ι⟩` and prove the remaining obligations. Simplify using `only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, map_zero]`. Conclude with `fun h => hx h.symm`. Introduce and unpack `⟨a, ha, hax⟩`.

Conclude with `ha hax`.
-/
theorem fractionRing_t2_of_openEmbedding {O : Type} [CommRing O] [IsDomain O]
    [TopologicalSpace O] [T2Space O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)]
    (he : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) : T2Space (FractionRing O) := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  set ι := algebraMap O (FractionRing O)
  have hsub : (ι ⁻¹' {x}).Subsingleton := fun a ha b hb => he.injective (ha.trans hb.symm)
  have hcl : IsClosed (ι ⁻¹' {x}) := hsub.isClosed
  refine ⟨ι '' (ι ⁻¹' {x})ᶜ, ?_, ?_⟩
  · refine (he.isOpenMap _ hcl.isOpen_compl).mem_nhds ⟨0, ?_, map_zero ι⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, map_zero]
    exact fun h => hx h.symm
  · rintro ⟨a, ha, hax⟩
    exact ha hax

/- English proof (translation)
Introduce `p O _ _ _ _ _ _ _ hO hF n`. Use `haveI := hO.t2`. Use `haveI := fractionRing_t2_of_openEmbedding hF.emb`. Use `set S := (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))`. Use `⟨?_, inferInstance, inferInstance⟩` and prove the remaining obligations.

Use `haveI : Module.Finite O (1 : Submodule O (FractionRing O)) := by`. Rewrite using `[Module.Finite.iff_fg, Submodule.one_eq_span]`. Conclude with `Submodule.fg_span (Set.finite_singleton _)`. Use `haveI : IsNoetherian O (1 : Submodule O (FractionRing O)) := inferInstance`. Set `f : S →ₗ[O] (1 : Submodule O (FractionRing O))` to `(LinearMap.lsmul O (FractionRing O) ((p : O) ^ n)).restrict (fun x hx => hx)`.

Use `Module.Finite.of_injective f ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `h` using `congrArg Subtype.val hab`. Simplify using `only [f, LinearMap.restrict_apply, LinearMap.lsmul_apply] at h`. Establish `hp : ((p : O) ^ n) ≠ 0` using `pow_ne_zero _ hO.p_ne`.

Conclude with `Subtype.ext (smul_right_injective (FractionRing O) hp h)`.
-/
theorem isFGTop_comap_lsmul_one : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)],
    PadicCoeff p O → FracTop O → ∀ n : ℕ,
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := by
  intro p O _ _ _ _ _ _ _ hO hF n
  haveI := hO.t2
  haveI := fractionRing_t2_of_openEmbedding hF.emb
  set S := (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))
  refine ⟨?_, inferInstance, inferInstance⟩
  haveI : Module.Finite O (1 : Submodule O (FractionRing O)) := by
    rw [Module.Finite.iff_fg, Submodule.one_eq_span]
    exact Submodule.fg_span (Set.finite_singleton _)
  haveI : IsNoetherian O (1 : Submodule O (FractionRing O)) := inferInstance
  let f : S →ₗ[O] (1 : Submodule O (FractionRing O)) :=
    (LinearMap.lsmul O (FractionRing O) ((p : O) ^ n)).restrict (fun x hx => hx)
  refine Module.Finite.of_injective f ?_
  intro a b hab
  have h := congrArg Subtype.val hab
  simp only [f, LinearMap.restrict_apply, LinearMap.lsmul_apply] at h
  have hp : ((p : O) ^ n) ≠ 0 := pow_ne_zero _ hO.p_ne
  exact Subtype.ext (smul_right_injective (FractionRing O) hp h)

end GlobalTheory
