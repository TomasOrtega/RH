import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PolynomialRingOverGlobalSections
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceGlobalSections
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def renameSumInl (k : Type u) [Field k] (M n : ℕ) :
    MvPolynomial (ULift.{u} (Fin M)) k →+* MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k :=
  (MvPolynomial.rename
      (fun a : ULift.{u} (Fin M) =>
        (ULift.up (Sum.inl a.down) : ULift.{u} (Fin M ⊕ Fin n)))).toRingHom

/- English proof (authored)
Renaming variables preserves all scalar coefficients, so it fixes a constant polynomial.
-/
theorem renameSumInl_C (k : Type u) [Field k] (M n : ℕ) (c : k) :
    renameSumInl k M n (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [renameSumInl]

/- English proof (authored)
Variable renaming takes each variable to the variable at its new index. Here the index is placed into the first block, so the image is the corresponding first-block variable.
-/
theorem renameSumInl_X (k : Type u) [Field k] (M n : ℕ) (a : Fin M) :
    renameSumInl k M n (MvPolynomial.X (ULift.up a)) =
      MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) := by
  simp [renameSumInl]

/- English proof (authored)
The two variables have indices in disjoint blocks. A coordinate variable has derivative zero with respect to a distinct variable.
-/
private theorem pderiv_inr_X_inl (k : Type u) [Field k] (M n : ℕ) (i : Fin n) (a : Fin M) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) = 0 := by
  classical
  simp [MvPolynomial.pderiv_X]

/- English proof (authored)
Check constants, sums and products with an original variable by polynomial induction. Constants have zero derivative, and additivity preserves vanishing. In the product case the renamed variable is in the first block, so its derivative in the second-block variable is zero. The other derivative in the product rule also vanishes by induction.
-/
theorem pderiv_inr_renameSumInl (k : Type u) [Field k] (M n : ℕ) (i : Fin n)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (renameSumInl k M n p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i c
    simp [renameSumInl_C]
  · rename_i q r hq hr
    simp [hq, hr]
  · rename_i q a hq
    obtain ⟨a⟩ := a
    rw [map_mul, renameSumInl_X, MvPolynomial.pderiv_mul, hq, pderiv_inr_X_inl]
    simp

/- English proof (authored)
The projection to the first block respects the field structure. Pulling a field section back through the projection and the first block's structure map is therefore the same as pulling it back along the full space's structure map.
-/
private theorem projLeft_appTop_affineSpaceIndexedByToSpec_appTop (k : Type u) [Field k] (M n : ℕ)
    (y : Γ(Spec (CommRingCat.of k), ⊤)) :
    (projLeft k M n).appTop ((affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y) =
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
  have h2 : ((projLeft k M n) ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y
      = (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
    rw [projLeft_comp_affineSpaceIndexedByToSpec]
  exact h2

/- English proof (authored)
Under the identification of polynomials with sections, a constant comes from the field by pullback. Projection to the first block preserves this pullback, so the constant corresponds to the same constant on the full affine space.
-/
private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_C (k : Type u) [Field k] (M n : ℕ) (c : k) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n)) (MvPolynomial.C c) := by
  rw [mvPolynomialEquivGlobalSections_C, mvPolynomialEquivGlobalSections_C, projLeft_appTop_affineSpaceIndexedByToSpec_appTop]

/- English proof (authored)
The polynomial variable corresponds to its coordinate section. Pullback along first-block projection gives the corresponding coordinate in the first block of the full space. The section identification sends the indicated variable to that coordinate.
-/
private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_X (k : Type u) [Field k] (M n : ℕ)
    (a : ULift.{u} (Fin M)) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a.down) : ULift.{u} (Fin M ⊕ Fin n))) := by
  obtain ⟨a⟩ := a
  simp

/- English proof (authored)
Compare the ring maps on constants and coordinate variables. Pullback along projection fixes constants and takes each original variable to the corresponding first-block variable. These are exactly the images under first-block renaming, so the two maps agree.
-/
theorem mvPolynomialEquivGlobalSections_symm_projLeft_appTop (k : Type u) [Field k] (M n : ℕ)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        ((projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) p)) =
      renameSumInl k M n p := by
  have key :
      ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm.toRingHom).comp
          ((((projLeft k M n).appTop).hom).comp
            ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).toRingHom))
        = renameSumInl k M n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)))
          = renameSumInl k M n (MvPolynomial.C c)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_C, RingEquiv.symm_apply_apply, renameSumInl_C]
    · intro a
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)))
          = renameSumInl k M n (MvPolynomial.X a)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_X, RingEquiv.symm_apply_apply]
      simp [renameSumInl]
  exact RingHom.congr_fun key p

/- English proof (authored)
On a coefficient section the map pulls back through the first projection and returns to polynomial coordinates, giving first-block renaming by the preceding calculation. On each new variable it returns the corresponding second-block variable. Evaluation with the stated coefficient map and variables has these same values, so the ring maps agree.
-/
theorem mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ) :
    ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm.toRingHom).comp (mvPolynomialToSumCoordinateRing k M n) =
      MvPolynomial.eval₂Hom
        ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom))
        (fun i : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))) := by
  apply MvPolynomial.ringHom_ext
  · intro t
    have h := mvPolynomialEquivGlobalSections_symm_projLeft_appTop k M n
      ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm t)
    simp only [RingEquiv.apply_symm_apply] at h
    simpa using h
  · intro i
    simp

/- English proof (authored)
Apply the equality of ring maps from the preceding statement to the specified polynomial. This gives the formula as evaluation with old coefficients in the first block and new variables in the second.
-/
theorem mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p) =
      MvPolynomial.eval₂
        ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom))
        (fun i : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))) p :=
  RingHom.congr_fun (mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing k M n) p

/- English proof (authored)
The derivative of every substituted coefficient vanishes by hypothesis. For a variable the derivative before and after substitution equals one at the selected index and zero at every other index. By additivity and the product rule the equality extends from constants and variables to all polynomials.
-/
private theorem pderiv_inr_eval₂_X_inr (k : Type u) [Field k] (M n : ℕ)
    (f : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
      MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) (i : Fin n)
    (hf : ∀ t, MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)) (f t) = 0)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.eval₂ f
          (fun j : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) p) =
      MvPolynomial.eval₂ f
        (fun j : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)))
        (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i t
    rw [MvPolynomial.eval₂_C, MvPolynomial.pderiv_C, MvPolynomial.eval₂_zero]
    exact hf t
  · rename_i q r hq hr
    simp [MvPolynomial.eval₂_add, hq, hr]
  · rename_i q j hq
    have hX : MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) =
        MvPolynomial.eval₂ f
          (fun l : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr l) : ULift.{u} (Fin M ⊕ Fin n)))
          (MvPolynomial.pderiv i (MvPolynomial.X j)) := by
      by_cases h : i = j
      · subst h
        simp
      · simp [MvPolynomial.pderiv_X, h]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.pderiv_mul,
      MvPolynomial.eval₂_add, hq, hX]

/- English proof (authored)
Express the coordinate-ring map in polynomial coordinates as evaluation, with coefficients included into the first block and variables in the second. Each substituted coefficient has zero derivative in a second-block variable by the first-block renaming result. Thus the differentiation rule for evaluation applies and gives the corresponding derivative of the original polynomial before substitution.
-/
theorem pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ) (i : Fin n)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p)) =
      (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv i p)) := by
  rw [mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing, mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing]
  refine pderiv_inr_eval₂_X_inr k M n
    ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom)) i ?_ p
  intro t
  rw [RingHom.comp_apply]
  exact pderiv_inr_renameSumInl k M n i _

end FunctorialResolution.EmbeddedResolution

end
