import Development.EtaleCohomology.EtaleSheaves.stupidPf

noncomputable section
open CategoryTheory Limits ZeroObject

namespace LateralTheory.E.trunc0Pf

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

/- English proof (translation)
Break down `lt_or_gt_of_ne hi with h | h` into its components or cases. Apply `HomologicalComplex.isZero_stupidTrunc_X` to reduce the goal to its premises. Introduce `j`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Conclude with `(K.isZero_of_isStrictlyLE 0 i h).of_iso (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := i.toNat) (by simp; omega))`.
-/
lemma isZero_tr (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (i : ℤ) (hi : i ≠ 0) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE 0)).X i) := by
  rcases lt_or_gt_of_ne hi with h | h
  · apply HomologicalComplex.isZero_stupidTrunc_X
    intro j; simp; omega
  · exact (K.isZero_of_isStrictlyLE 0 i h).of_iso
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := i.toNat) (by simp; omega))

/- English proof (translation)
The claim follows from `HomologicalComplex.single_map_f_self _ _ f`.
-/
lemma cochainComplex_singleFunctor_zero_map_f_zero {A B : C} (f : A ⟶ B) :
    ((CochainComplex.singleFunctor C 0).map f).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv :=
  HomologicalComplex.single_map_f_self _ _ f

def eIso (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE 0) ≅ (CochainComplex.singleFunctor C 0).obj (K.X 0) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if h : i = 0 then (by
        subst h
        exact K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp) ≪≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).symm)
      else (isZero_tr K i h).iso (HomologicalComplex.isZero_single_obj_X _ 0 _ i h))
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      by_cases hj : j = 0
      · exact (isZero_tr K i (by omega)).eq_of_src _ _
      · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ j hj).eq_of_tgt _ _)

/- English proof (translation)
Apply the tactic sequence `simp [eIso] <;> rfl`.
-/
lemma stupidTruncGEZeroIsoSingle_hom_f_zero (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    (eIso K).hom.f 0 = (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp)).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).inv := by
  simp [eIso] <;> rfl

/- English proof (translation)
Use extensionality with `i`. Distinguish the cases in `h : i = 0`. Substitute `h` using the available equality. Simplify using `only [HomologicalComplex.comp_f, stupidTruncGEZeroIsoSingle_hom_f_zero, cochainComplex_singleFunctor_zero_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc]`. Use `erw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom_assoc]`.

Use `first`. Consider the case `(apply Eq.symm; refine (Category.assoc _ _ _).trans ?_; congr 1; exact Iso.inv_hom_id_assoc _ _)`. Consider the case `(dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors] at *; simp)`. Conclude with `(HomologicalComplex.isZero_single_obj_X _ 0 _ i h).eq_of_tgt _ _`.
-/
lemma nat {K L : CochainComplex C ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE 0) ≫ (eIso L).hom =
      (eIso K).hom ≫ (CochainComplex.singleFunctor C 0).map (g.f 0) := by
  ext i
  by_cases h : i = 0
  · subst h
    simp only [HomologicalComplex.comp_f, stupidTruncGEZeroIsoSingle_hom_f_zero, cochainComplex_singleFunctor_zero_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc]
    erw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom_assoc]
    first
    | (apply Eq.symm; refine (Category.assoc _ _ _).trans ?_; congr 1; exact Iso.inv_hom_id_assoc _ _)
    | (dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors] at *; simp)
  · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ i h).eq_of_tgt _ _

/- English proof (translation)
Introduce `R _ K L _ _ g`. Conclude with `⟨eIso K, eIso L, nat g⟩`.
-/
theorem trunc0_of : LateralTheory.E.stupidPf.trunc0 := by
  intro R _ K L _ _ g
  exact ⟨eIso K, eIso L, nat g⟩

end LateralTheory.E.trunc0Pf
