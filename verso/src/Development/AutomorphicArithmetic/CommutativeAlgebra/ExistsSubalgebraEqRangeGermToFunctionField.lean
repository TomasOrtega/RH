import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

/- English proof (translation)
Introduce `k _ C _ c _ h W _`. Establish `hη : genericPoint C ∈ (⊤ : C.Opens)` using `trivial`. Establish `key : CommRingCat.ofHom (algebraMap k C.functionField) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) hη`. Rewrite using `[← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).hom, ← Scheme.ΓSpecIso_naturality, h]`. Simplify using `only [Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id_assoc]`.

Use `congr 1`. Rewrite using `[Scheme.fromSpecStalk_appTop]`. Establish `e1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)) = 𝟙 _` using `Subsingleton.elim _ _`. Rewrite using `[e1, op_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]`. Conclude with `congrArg (C.presheaf.germ ⊤ (genericPoint C) _ ≫ ·) (Iso.inv_hom_id _) |>.trans (Category.comp_id _)`.

Use `⟨{ (C.germToFunctionField W).hom.range with algebraMap_mem' := ?_ }, ?_⟩` and prove the remaining obligations. Introduce `r`. Use `⟨C.presheaf.map (homOfLE le_top).op (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)), ?_⟩` and prove the remaining obligations. Establish `hr` using `congrArg (fun f => f.hom r) key`. Simplify using `only [CommRingCat.hom_ofHom, CommRingCat.comp_apply] at hr`.

Rewrite using `[hr]`. Conclude with `C.presheaf.germ_res_apply (homOfLE le_top) _ _ _`. Both sides reduce to the same expression.
-/
theorem UpperTheory.exists_subalgebra_eq_range_germToFunctionField :
    ∀ (k : Type) [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], ∃ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) := by
  intro k _ C _ c _ h W _
  have hη : genericPoint C ∈ (⊤ : C.Opens) := trivial
  have key : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) hη := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).hom, ← Scheme.ΓSpecIso_naturality, h]
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id_assoc]
    congr 1
    rw [Scheme.fromSpecStalk_appTop]
    have e1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [e1, op_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
    exact congrArg (C.presheaf.germ ⊤ (genericPoint C) _ ≫ ·) (Iso.inv_hom_id _) |>.trans
      (Category.comp_id _)
  refine ⟨{ (C.germToFunctionField W).hom.range with algebraMap_mem' := ?_ }, ?_⟩
  · intro r
    refine ⟨C.presheaf.map (homOfLE le_top).op (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)), ?_⟩
    have hr := congrArg (fun f => f.hom r) key
    simp only [CommRingCat.hom_ofHom, CommRingCat.comp_apply] at hr
    rw [hr]
    exact C.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  · rfl
