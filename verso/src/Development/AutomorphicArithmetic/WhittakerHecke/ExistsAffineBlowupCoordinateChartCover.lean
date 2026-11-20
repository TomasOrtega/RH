import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open FunctorialResolution.Blowup FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Rewrite using `[opensRange_affineBlowupChart_eq_basicOpen, affineBlowupChart_eq_awayι]`. Use `(Proj.awayι_preimage_basicOpen (reesGrading I) (reesGenerator_mem_reesGrading I c) Nat.one_pos (reesGenerator_mem_reesGrading I a) Nat.one_pos).trans ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[chartFraction_eq_mk]`. Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises.

Simplify using `[HomogeneousLocalization.Away.mk]`.
-/
private theorem chart_preimage_opensRange {R : Type} [CommRing R] (I : Ideal R) (c a : ↥I) :
    affineBlowupChart I c ⁻¹ᵁ (affineBlowupChart I a).opensRange
      = PrimeSpectrum.basicOpen (chartFraction I c a) := by
  rw [opensRange_affineBlowupChart_eq_basicOpen, affineBlowupChart_eq_awayι]
  refine (Proj.awayι_preimage_basicOpen (reesGrading I) (reesGenerator_mem_reesGrading I c) Nat.one_pos
    (reesGenerator_mem_reesGrading I a) Nat.one_pos).trans ?_
  congr 1
  rw [chartFraction_eq_mk]
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.mk]

/- English proof (translation)
Establish `hcomp` using `awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst A (Finset.univ : Finset (Fin D)) j (Finset.mem_univ j)`. Establish `hk` using `RingHom.congr_fun hcomp (MvPolynomial.X k)`. Establish `hj` using `RingHom.congr_fun hcomp (MvPolynomial.X j)`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe] at hk hj`. Rewrite `hk` using `[coordBlowupSubst_X_of_mem A _ j (Finset.mem_univ k) hkj, map_mul]`.

Rewrite `hj` using `[coordBlowupSubst_X_self]`. Establish `h3` using `chartRingHom_coe_eq_chartFraction_mul (coordIdeal A (Finset.univ : Finset (Fin D))) (coordIdealGen A Finset.univ j (Finset.mem_univ j)) (coordIdealGen A Finset.univ k (Finset.mem_univ k))`. Establish `hnz` using `chartRingHom_mem_nonZeroDivisors (coordIdeal A (Finset.univ : Finset (Fin D))) (coordIdealGen A Finset.univ j (Finset.mem_univ j))`. Rewrite `h3`, `hnz` using `[coe_coordIdealGen]`. Rewrite `h3` using `[coe_coordIdealGen]`.

Rewrite `hnz`, `h3` using `[← hj]`. Rewrite `h3` using `[← hk]`. Conclude with `(mul_cancel_right_mem_nonZeroDivisors hnz).mp h3`.
-/
private theorem equiv_symm_X {A : Type} [CommRing A] {D : ℕ} (j k : Fin D) (hkj : k ≠ j) :
    (awayCoordGenEquivMvPolynomial A (Finset.univ : Finset (Fin D)) j (Finset.mem_univ j)).symm
        (MvPolynomial.X k)
      = chartFraction (coordIdeal A (Finset.univ : Finset (Fin D)))
          (coordIdealGen A Finset.univ j (Finset.mem_univ j))
          (coordIdealGen A Finset.univ k (Finset.mem_univ k)) := by
  have hcomp := awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst A
    (Finset.univ : Finset (Fin D)) j (Finset.mem_univ j)
  have hk := RingHom.congr_fun hcomp (MvPolynomial.X k)
  have hj := RingHom.congr_fun hcomp (MvPolynomial.X j)
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.toRingHom_eq_coe] at hk hj
  rw [coordBlowupSubst_X_of_mem A _ j (Finset.mem_univ k) hkj, map_mul] at hk
  rw [coordBlowupSubst_X_self] at hj
  have h3 := chartRingHom_coe_eq_chartFraction_mul (coordIdeal A (Finset.univ : Finset (Fin D)))
    (coordIdealGen A Finset.univ j (Finset.mem_univ j)) (coordIdealGen A Finset.univ k (Finset.mem_univ k))
  have hnz := chartRingHom_mem_nonZeroDivisors (coordIdeal A (Finset.univ : Finset (Fin D)))
    (coordIdealGen A Finset.univ j (Finset.mem_univ j))
  rw [coe_coordIdealGen] at h3 hnz
  rw [coe_coordIdealGen] at h3
  rw [← hj] at hnz h3
  rw [← hk] at h3
  exact (mul_cancel_right_mem_nonZeroDivisors hnz).mp h3

/- English proof (translation)
Introduce `A _ D`. Set `I` to `coordIdeal A (Finset.univ : Finset (Fin D))`. Set `e : ∀ j : Fin D, _` to `fun j => awayCoordGenEquivMvPolynomial A (Finset.univ : Finset (Fin D)) j (Finset.mem_univ j)`. Use `⟨fun j => Spec.map (e j).toCommRingCatIso.hom ≫ affineBlowupChart I (coordIdealGen A Finset.univ j (Finset.mem_univ j)), fun j => inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`.

Rewrite using `[Category.assoc, affineBlowupChart_comp_toSpec, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `x : 1`. Establish `hcomp` using `awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst A (Finset.univ : Finset (Fin D)) j (Finset.mem_univ j)`. Rewrite using `[algebraMap_chart_eq_chartRingHom, ← hcomp]`.

Simplify using `[e]`. Apply `top_unique` to reduce the goal to its premises. Rewrite using `[← iSup_opensRange_affineBlowupChart_coordIdealGen A (Finset.univ : Finset (Fin D))]`. Use `iSup_le fun i => le_iSup_of_le i.1 ?_` and prove the remaining obligations. Rewrite using `[Scheme.Hom.opensRange_comp_of_isIso]`.

Introduce `j k`. Rewrite using `[Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.comp_preimage, chart_preimage_opensRange, SpecMap_preimage_basicOpen]`. Use `split_ifs with hkj`. Substitute `hkj` using the available equality. Establish `h1 : chartFraction I (coordIdealGen A Finset.univ k (Finset.mem_univ k)) (coordIdealGen A Finset.univ k (Finset.mem_univ k)) = 1`.

Rewrite using `[chartFraction_eq_mk]`. Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `[h1]`. Both sides reduce to the same expression.

Establish `h2` using `equiv_symm_X (A := A) j k hkj`. Rewrite using `[← h2]`. Simplify using `[e]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.exists_affineBlowup_coordinate_chart_cover :
    ∀ (A : Type) [CommRing A] (D : ℕ),
        ∃ (c : Fin D → (Spec (CommRingCat.of (MvPolynomial (Fin D) A)) ⟶
            affineBlowup (coordIdeal A (Finset.univ : Finset (Fin D))))) (_ : ∀ j, IsOpenImmersion (c j)),
          (∀ j, c j ≫ AffineBlowup.toSpec (coordIdeal A (Finset.univ : Finset (Fin D))) =
            Spec.map (CommRingCat.ofHom (coordBlowupSubst A Finset.univ j).toRingHom)) ∧
          (⨆ j, (c j).opensRange = ⊤) ∧
          ∀ j k, c j ⁻¹ᵁ (c k).opensRange =
            PrimeSpectrum.basicOpen (if k = j then (1 : MvPolynomial (Fin D) A) else MvPolynomial.X k) := by
  intro A _ D
  classical
  let I := coordIdeal A (Finset.univ : Finset (Fin D))
  let e : ∀ j : Fin D, _ := fun j =>
    awayCoordGenEquivMvPolynomial A (Finset.univ : Finset (Fin D)) j (Finset.mem_univ j)
  refine ⟨fun j => Spec.map (e j).toCommRingCatIso.hom ≫
    affineBlowupChart I (coordIdealGen A Finset.univ j (Finset.mem_univ j)), fun j => inferInstance,
    ?_, ?_, ?_⟩
  · intro j
    rw [Category.assoc, affineBlowupChart_comp_toSpec, ← Spec.map_comp]
    congr 1
    ext x : 1
    have hcomp := awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst A
      (Finset.univ : Finset (Fin D)) j (Finset.mem_univ j)
    rw [algebraMap_chart_eq_chartRingHom, ← hcomp]
    simp [e]
  · apply top_unique
    rw [← iSup_opensRange_affineBlowupChart_coordIdealGen A (Finset.univ : Finset (Fin D))]
    refine iSup_le fun i => le_iSup_of_le i.1 ?_
    rw [Scheme.Hom.opensRange_comp_of_isIso]
  · intro j k
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.comp_preimage, chart_preimage_opensRange,
      SpecMap_preimage_basicOpen]
    split_ifs with hkj
    · subst hkj
      have h1 : chartFraction I (coordIdealGen A Finset.univ k (Finset.mem_univ k))
          (coordIdealGen A Finset.univ k (Finset.mem_univ k)) = 1 := by
        rw [chartFraction_eq_mk]
        apply HomogeneousLocalization.val_injective
        simp
      simp [h1]
      rfl
    · have h2 := equiv_symm_X (A := A) j k hkj
      rw [← h2]
      simp [e]
      rfl
