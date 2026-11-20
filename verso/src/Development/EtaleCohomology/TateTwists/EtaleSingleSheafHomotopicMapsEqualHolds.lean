import Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ F I _ a b ⟨h⟩`. Apply `HomologicalComplex.hom_ext` to reduce the goal to its premises. Introduce `i`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality.

Rewrite using `[h.comm 0]`. Establish `h1 : dNext 0 h.hom = 0`. Rewrite using `[dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp)]`. Rewrite using `[show (sgl F).d 0 1 = 0 from (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by omega)).eq_of_tgt _ _]`. Simplify using the standard rewrite rules.

Establish `h2 : prevD 0 h.hom = 0`. Rewrite using `[prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]`. Rewrite using `[show h.hom 0 (-1) = 0 from (CochainComplex.isZero_of_isStrictlyGE I 0 (-1) (by omega)).eq_of_tgt _ _]`. Simplify using the standard rewrite rules. Rewrite using `[h1, h2]`.

Simplify using the standard rewrite rules. Conclude with `(HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i hi).eq_of_src _ _`.
-/
theorem LateralTheory.EtaleFoundations.etale_single_sheaf_homotopic_maps_equal_holds : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual := by
  intro R _ F I _ a b ⟨h⟩
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
    rw [h.comm 0]
    have h1 : dNext 0 h.hom = 0 := by
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp)]
      rw [show (sgl F).d 0 1 = 0 from
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by omega)).eq_of_tgt _ _]
      simp
    have h2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
      rw [show h.hom 0 (-1) = 0 from (CochainComplex.isZero_of_isStrictlyGE I 0 (-1) (by omega)).eq_of_tgt _ _]
      simp
    rw [h1, h2]; simp
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i hi).eq_of_src _ _
