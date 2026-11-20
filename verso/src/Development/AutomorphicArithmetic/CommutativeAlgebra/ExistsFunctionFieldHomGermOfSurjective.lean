import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

/- English proof (translation)
Introduce `C X _ _ u hu`. Establish `hgX : closure ({genericPoint X} : Set X) = Set.univ` using `genericPoint_spec X`. Establish `hcl : closure ({u (genericPoint X)} : Set C) = Set.univ`. Apply `Set.eq_univ_of_univ_subset` to reduce the goal to its premises. Establish `h1` using `image_closure_subset_closure_image (s := ({genericPoint X} : Set X)) u.continuous`.

Rewrite `h1` using `[Set.image_singleton, hgX, Set.image_univ, (Surjective.surj (f := u)).range_eq]`. Conclude with `h1`. Establish `hsp : u (genericPoint X) ⤳ genericPoint C`. Rewrite using `[specializes_iff_mem_closure, hcl]`. Discharge the goal by the elementary cases of `trivial`.

Use `⟨(C.presheaf.stalkSpecializes hsp ≫ u.stalkMap (genericPoint X)).hom, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]`. Introduce `W _ _ a`. Establish `hmem : u (genericPoint X) ∈ W` using `((genericPoint_spec X).mem_open_set_iff (u ⁻¹ᵁ W).isOpen).mpr (by simpa using ‹Nonempty (u ⁻¹ᵁ W)›)`. Express the relevant statement in the definitionally equal form `(u.stalkMap (genericPoint X)).hom ((C.presheaf.stalkSpecializes hsp).hom ((C.presheaf.germ W (genericPoint C) _).hom a)) = _`.

Rewrite using `[TopCat.Presheaf.germ_stalkSpecializes_apply (hy := _) (h := hsp)]`. Conclude with `Scheme.Hom.germ_stalkMap_apply u W (genericPoint X) hmem a`.
-/
theorem UpperTheory.exists_functionField_hom_germ_of_surjective :
    ∀ {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (u : X ⟶ C), Surjective u → ∃ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u ∧ ∀ (W : C.Opens) [Nonempty W] [Nonempty (u ⁻¹ᵁ W)] (a : Γ(C, W)), φ (C.germToFunctionField W a) = X.germToFunctionField (u ⁻¹ᵁ W) (u.app W a) := by
  intro C X _ _ u hu
  have hgX : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hcl : closure ({u (genericPoint X)} : Set C) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    have h1 := image_closure_subset_closure_image (s := ({genericPoint X} : Set X)) u.continuous
    rw [Set.image_singleton, hgX, Set.image_univ,
      (Surjective.surj (f := u)).range_eq] at h1
    exact h1
  have hsp : u (genericPoint X) ⤳ genericPoint C := by
    rw [specializes_iff_mem_closure, hcl]
    trivial
  refine ⟨(C.presheaf.stalkSpecializes hsp ≫ u.stalkMap (genericPoint X)).hom, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · intro W _ _ a
    have hmem : u (genericPoint X) ∈ W :=
      ((genericPoint_spec X).mem_open_set_iff (u ⁻¹ᵁ W).isOpen).mpr (by simpa using ‹Nonempty (u ⁻¹ᵁ W)›)
    change (u.stalkMap (genericPoint X)).hom ((C.presheaf.stalkSpecializes hsp).hom
      ((C.presheaf.germ W (genericPoint C) _).hom a)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply (hy := _) (h := hsp)]
    exact Scheme.Hom.germ_stalkMap_apply u W (genericPoint X) hmem a
