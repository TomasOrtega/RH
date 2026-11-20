import Mathlib

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem discreteTopology_of_isOpen_of_forall_mem {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (H : AddSubgroup G) (U : Set G) (hU : IsOpen U) (h0 : (0 : G) ∈ U)
    (hH : ∀ x ∈ H, x ∈ U → x = 0) : DiscreteTopology H := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert hU.preimage continuous_subtype_val
  ext ⟨x, hx⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro h
    have hx0 : x = 0 := by simpa using congrArg Subtype.val h
    rw [hx0]
    exact h0
  · intro h
    exact Subtype.ext (hH x hx h)

variable (K : Type*) [Field K]

open scoped Classical in

noncomputable def homeomorphMixedSpace : K∞ ≃ₜ mixedEmbedding.mixedSpace K :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace K => IsReal v)
      (fun v => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun v => (isometryEquivRealOfIsReal v.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun v =>
          (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex))))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homeomorphMixedSpace_apply (x : K∞) :
    homeomorphMixedSpace K x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem homeomorphMixedSpace_algebraMap (k : K) :
    homeomorphMixedSpace K (algebraMap K K∞ k) = mixedEmbedding K k := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem homeomorphMixedSpace_sub (x y : K∞) :
    homeomorphMixedSpace K (x - y) = homeomorphMixedSpace K x - homeomorphMixedSpace K y := by
  simp only [homeomorphMixedSpace_apply, map_sub]

variable [NumberField K]

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem eq_zero_of_forall_infinitePlace_lt_one (z : 𝓞 K) (h : ∀ w : InfinitePlace K, w z < 1) :
    z = 0 := by
  by_contra hz
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact (one_le_of_lt_one hz fun w' _ => h w').not_gt (h w)

omit [NumberField K] in
/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem norm_algebraMap_apply (k : K) (w : InfinitePlace K) :
    ‖algebraMap K K∞ k w‖ = w k := by
  simp [InfiniteAdeleRing.algebraMap_apply, WithAbs.norm_toAbs_eq]
  rfl

noncomputable def integersInfinite : AddSubgroup K∞ :=
  (algebraMap (𝓞 K) K∞).range.toAddSubgroup

open scoped Classical

noncomputable def fundamentalSetInfinite : Set K∞ :=
  homeomorphMixedSpace K ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isCompact_closure_fundamentalSetInfinite :
    IsCompact (closure (fundamentalSetInfinite K)) := by
  rw [fundamentalSetInfinite, ← Homeomorph.preimage_closure, Homeomorph.isCompact_preimage]
  exact (ZSpan.fundamentalDomain_isBounded _).isCompact_closure

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem existsUnique_sub_mem_fundamentalSetInfinite (x : K∞) :
    ∃! z : 𝓞 K, x - algebraMap (𝓞 K) K∞ z ∈ fundamentalSetInfinite K := by
  set b := mixedEmbedding.latticeBasis K
  have hmem : ∀ z : 𝓞 K, mixedEmbedding K (z : K) ∈ Submodule.span ℤ (Set.range b) := by
    intro z
    rw [mixedEmbedding.mem_span_latticeBasis]
    exact ⟨z, rfl⟩
  have himg : ∀ z : 𝓞 K, homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z) =
      homeomorphMixedSpace K x - mixedEmbedding K (z : K) := by
    intro z
    rw [homeomorphMixedSpace_sub, IsScalarTower.algebraMap_apply (𝓞 K) K K∞,
      homeomorphMixedSpace_algebraMap]
  have hinj : Function.Injective fun z : 𝓞 K => mixedEmbedding K (z : K) :=
    (mixedEmbedding K).injective.comp RingOfIntegers.coe_injective
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 K, mixedEmbedding K (z : K) =
      (ZSpan.floor b (homeomorphMixedSpace K x) : mixedEmbedding.mixedSpace K) := by
    have := (ZSpan.floor b (homeomorphMixedSpace K x)).2
    rw [mixedEmbedding.mem_span_latticeBasis] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz⟩
  refine ⟨z, ?_, fun z' hz' => ?_⟩
  · change homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z) ∈ ZSpan.fundamentalDomain b
    rw [himg, hz]
    exact ZSpan.fract_mem_fundamentalDomain b _
  · replace hz' : homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z') ∈
        ZSpan.fundamentalDomain b := hz'
    rw [himg] at hz'
    have h1 : homeomorphMixedSpace K x - mixedEmbedding K (z : K) ∈ ZSpan.fundamentalDomain b := by
      rw [hz]
      exact ZSpan.fract_mem_fundamentalDomain b _
    rw [← ZSpan.fract_eq_self] at h1 hz'
    have heq : ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) =
        ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) := by
      rw [ZSpan.fract_eq_fract]
      have : -(homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) +
          (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) =
          mixedEmbedding K (z' : K) - mixedEmbedding K (z : K) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hmem z') (hmem z)
    rw [hz', h1] at heq
    exact hinj (sub_right_injective heq)

end GroundTheory.Global
