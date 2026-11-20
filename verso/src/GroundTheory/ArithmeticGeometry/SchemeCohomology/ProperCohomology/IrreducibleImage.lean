import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SchemeImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

noncomputable section

/- English proof (translation)
Apply `isIso_of_isOpenImmersion_of_opensRange_eq_top` to reduce the goal to its premises. Apply `le_antisymm le_top` to reduce the goal to its premises. Introduce `x _`. Use `⟨⟨x, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `O.ι x ∈ O`.

Conclude with `x.2`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `morphismRestrict_base_coe O.ι O ⟨x, _⟩`.
-/
lemma isIso_opens_ι_restrict {Z : Scheme.{u}} (O : Z.Opens) : IsIso (O.ι ∣_ O) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply le_antisymm le_top
  intro x _
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change O.ι x ∈ O
    exact x.2
  · apply Subtype.ext
    exact morphismRestrict_base_coe O.ι O ⟨x, _⟩

/- English proof (translation)
Take `⟨z⟩` from `‹Nonempty Z›`. Establish `hC` using `irreducibleComponent_mem_irreducibleComponents z`. Use `set C := irreducibleComponent z`. Use `set O := Z.irreducibleComponentOpen C`. Use `⟨Z.irreducibleComponent C hC, Z.irreducibleComponentι C hC, O, inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨o, ho, hne, hoC⟩` from `NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Establish `hcl` using `closure_sUnion_irreducibleComponents_sdiff_singleton NoetherianSpace.finite_irreducibleComponents C hC`. Establish `: (O : Set Z) = (⋃₀ (irreducibleComponents Z \ {C}))ᶜ` using `rfl`.

Rewrite `h` using `[this, Set.compl_empty_iff]`. Rewrite `hcl` using `[h, Set.compl_univ, closure_empty]`. Conclude with `hC.1.nonempty.ne_empty hcl.symm`. Establish `hI` using `Z.irreducibleComponentIdeal_def C hC`. Establish `: IsIso (O.ι ∣_ O)` using `isIso_opens_ι_restrict O`.

Establish `key` using `SchemeImage.imageRestrictLift_fac O.ι O`. Express the relevant statement in the definitionally equal form `IsIso ((Z.irreducibleComponentIdeal C hC).subschemeι ∣_ O)`. Rewrite using `[hI]`. Express the relevant statement in the definitionally equal form `IsIso (O.ι.imageι ∣_ O)`. Rewrite using `[← key]`.

Use `infer_instance`.
-/
theorem exists_irreducible_isIso_restrict (Z : Scheme.{u}) [IsNoetherian Z] [Nonempty Z] :
    ∃ (Z₁ : Scheme.{u}) (c : Z₁ ⟶ Z) (O : Z.Opens), IsClosedImmersion c ∧ IrreducibleSpace Z₁ ∧
      (O : Set Z).Nonempty ∧ IsIso (c ∣_ O) := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  have hC := irreducibleComponent_mem_irreducibleComponents z
  set C := irreducibleComponent z
  set O := Z.irreducibleComponentOpen C
  refine ⟨Z.irreducibleComponent C hC, Z.irreducibleComponentι C hC, O, inferInstance,
    inferInstance, ?_, ?_⟩
  · obtain ⟨o, ho, hne, hoC⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC

    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents C hC
    have : (O : Set Z) = (⋃₀ (irreducibleComponents Z \ {C}))ᶜ := rfl
    rw [this, Set.compl_empty_iff] at h
    rw [h, Set.compl_univ, closure_empty] at hcl
    exact hC.1.nonempty.ne_empty hcl.symm
  · have hI := Z.irreducibleComponentIdeal_def C hC
    have : IsIso (O.ι ∣_ O) := isIso_opens_ι_restrict O
    have key := SchemeImage.imageRestrictLift_fac O.ι O
    change IsIso ((Z.irreducibleComponentIdeal C hC).subschemeι ∣_ O)
    rw [hI]
    change IsIso (O.ι.imageι ∣_ O)
    rw [← key]
    infer_instance

end

end GroundTheory.Arith.SchemeCoh
