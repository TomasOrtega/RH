import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def specHomOfGlobalSections (A : Scheme.{u}) [AlgebraicGeometry.IsAffine A] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') : Spec B' ⟶ A :=
  Spec.map σ ≫ A.isoSpec.inv

@[simp]
/- English proof (authored)
The scheme map is obtained by taking spectra of the ring map and identifying the spectrum of the ambient global sections with the affine ambient scheme. Naturality of the identification between rings and sections on spectra shows that pullback sends a section to its image under the given ring map, viewed as a section on the source spectrum.
-/
theorem specHomOfGlobalSections_appTop (A : Scheme.{u}) [AlgebraicGeometry.IsAffine A]
    {B' : CommRingCat.{u}} (σ : Γ(A, ⊤) ⟶ B') (s : Γ(A, ⊤)) :
    (specHomOfGlobalSections A σ).appTop s = (Scheme.ΓSpecIso B').inv (σ s) := by
  have hcomp : specHomOfGlobalSections A σ ≫ A.isoSpec.hom = Spec.map σ := by
    simp [specHomOfGlobalSections]
  have h : (Scheme.ΓSpecIso Γ(A, ⊤)).hom ≫ (specHomOfGlobalSections A σ).appTop
      = (Spec.map σ).appTop := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, hcomp]
  have h3 : (specHomOfGlobalSections A σ).appTop = σ ≫ (Scheme.ΓSpecIso B').inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(A, ⊤)).hom, Scheme.ΓSpecIso_inv_naturality,
      Iso.hom_inv_id_assoc]
    exact h
  rw [h3, CommRingCat.comp_apply]

def specToAffineSpaceExtendCoords (k : Type u) [Field k] (A : Scheme.{u}) [AlgebraicGeometry.IsAffine A]
    (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') :
    Spec B' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)) :=
  AffineSpace.homOfVector (specHomOfGlobalSections A σ ≫ pA)
    (fun i =>
      Sum.elim
        (fun a : Fin M =>
          (specHomOfGlobalSections A σ ≫ e).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a)))
        (fun j : Fin n => (Scheme.ΓSpecIso B').inv (b j))
        i.down)

@[simp]
/- English proof (authored)
The map determined by the two blocks of sections is constructed over the field, using the structural map obtained through the ambient scheme. Its composite with the target projection is that structural map.
-/
theorem specToAffineSpaceExtendCoords_comp_toSpec (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') :
    specToAffineSpaceExtendCoords k A pA M e σ n b ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n)) =
      specHomOfGlobalSections A σ ≫ pA := by
  simp [specToAffineSpaceExtendCoords]

@[simp]
/- English proof (authored)
In the first coordinate block, the defining sections are the pullbacks of the original affine-space coordinates along the map through the ambient scheme. The coordinate formula for a map into affine space gives exactly these sections.
-/
theorem specToAffineSpaceExtendCoords_appTop_coord_inl (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') (a : Fin M) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n))) =
      (specHomOfGlobalSections A σ ≫ e).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a)) := by
  simp [specToAffineSpaceExtendCoords]

@[simp]
/- English proof (authored)
The defining vector uses the sections corresponding to the given ring elements as its second block. Pullback of the coordinate in this block returns its defining section.
-/
theorem specToAffineSpaceExtendCoords_appTop_coord_inr (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') (j : Fin n) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) =
      (Scheme.ΓSpecIso B').inv (b j) := by
  simp [specToAffineSpaceExtendCoords]

/- English proof (authored)
After projection to the first block, both maps have the same structural map by the hypothesis that the ambient embedding is over the field. Their pullbacks of the first-block coordinates agree by construction. The coordinate characterization of maps into affine space gives equality.
-/
theorem specToAffineSpaceExtendCoords_comp_projLeft (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA) :
    specToAffineSpaceExtendCoords k A pA M e σ n b ≫ projLeft k M n = specHomOfGlobalSections A σ ≫ e := by
  refine AffineSpace.hom_ext ?_ ?_
  · simp [he]
  · rintro ⟨a⟩
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord,
      specToAffineSpaceExtendCoords_appTop_coord_inl]

/- English proof (authored)
The closed immersion of the ambient scheme induces a surjection on global sections. Lift each ambient coefficient to a section of the first affine space and then pull that section back along projection from the larger affine space. The first-block comparison ensures its image is the corresponding coefficient in the target ring. Each new generator is the pullback of its second-block coordinate. Thus sums and products of these lifted coordinates and coefficients give preimages of all polynomial expressions in the generators. By the generation hypothesis these expressions give every global section of the source spectrum.
-/
theorem specToAffineSpaceExtendCoords_appTop_surjective (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA)
    (hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.eval₂ σ.hom b p = x) :
    Function.Surjective ⇑((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop) := by
  have hsurj : Function.Surjective ⇑(e.appTop) :=
    (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine e).2
  have hproj : specToAffineSpaceExtendCoords k A pA M e σ n b ≫ projLeft k M n
      = specHomOfGlobalSections A σ ≫ e := specToAffineSpaceExtendCoords_comp_projLeft k A pA M e σ n b he
  have hsec : ∀ s : Γ(A, ⊤), ∃ P, (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop P
      = (Scheme.ΓSpecIso B').inv (σ s) := by
    intro s
    obtain ⟨P, hPs⟩ := hsurj s
    refine ⟨(projLeft k M n).appTop P, ?_⟩
    have h2 := congrArg
      (fun g : Spec B' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)) => g.appTop P) hproj
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h2
    rw [h2, hPs, specHomOfGlobalSections_appTop]
  have key : ∀ p : MvPolynomial (Fin n) Γ(A, ⊤), ∃ P,
      (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop P
        = (Scheme.ΓSpecIso B').inv (MvPolynomial.eval₂ σ.hom b p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C s =>
        obtain ⟨P, hP⟩ := hsec s
        refine ⟨P, ?_⟩
        rw [MvPolynomial.eval₂_C]
        exact hP
    | add p q hp hq =>
        obtain ⟨P, hP⟩ := hp
        obtain ⟨Q, hQ⟩ := hq
        refine ⟨P + Q, ?_⟩
        rw [map_add, MvPolynomial.eval₂_add, map_add, hP, hQ]
    | mul_X p j hp =>
        obtain ⟨P, hP⟩ := hp
        refine ⟨P * AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)), ?_⟩
        rw [map_mul, hP, specToAffineSpaceExtendCoords_appTop_coord_inr, MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_X, map_mul]
  intro y
  obtain ⟨p, hp⟩ := hgen ((Scheme.ΓSpecIso B').hom y)
  obtain ⟨P, hP⟩ := key p
  refine ⟨P, ?_⟩
  rw [hP, hp]
  simp

/- English proof (authored)
Both schemes are affine and the map on global sections is surjective by the coordinate generation result. For affine schemes, such a map defines a closed immersion.
-/
theorem isClosedImmersion_specToAffineSpaceExtendCoords (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA)
    (hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.eval₂ σ.hom b p = x) :
    AlgebraicGeometry.IsClosedImmersion (specToAffineSpaceExtendCoords k A pA M e σ n b) :=
  AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine _
    (specToAffineSpaceExtendCoords_appTop_surjective k A pA M e σ n b he hgen)

end FunctorialResolution.EmbeddedResolution

end
