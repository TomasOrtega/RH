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
/- English proof (translation)
Establish `hcomp : specHomOfGlobalSections A σ ≫ A.isoSpec.hom = Spec.map σ`. Simplify using `[specHomOfGlobalSections]`. Establish `h : (Scheme.ΓSpecIso Γ(A, ⊤)).hom ≫ (specHomOfGlobalSections A σ).appTop = (Spec.map σ).appTop`. Rewrite using `[← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, hcomp]`. Establish `h3 : (specHomOfGlobalSections A σ).appTop = σ ≫ (Scheme.ΓSpecIso B').inv`.

Rewrite using `[← cancel_epi (Scheme.ΓSpecIso Γ(A, ⊤)).hom, Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]`. Conclude with `h`. Rewrite using `[h3, CommRingCat.comp_apply]`.
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
/- English proof (translation)
Simplify using `[specToAffineSpaceExtendCoords]`. Use the proof step `@[simp]`.
-/
theorem specToAffineSpaceExtendCoords_comp_toSpec (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') :
    specToAffineSpaceExtendCoords k A pA M e σ n b ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n)) =
      specHomOfGlobalSections A σ ≫ pA := by
  simp [specToAffineSpaceExtendCoords]

@[simp]
/- English proof (translation)
Simplify using `[specToAffineSpaceExtendCoords]`. Use the proof step `@[simp]`.
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
/- English proof (translation)
Simplify using `[specToAffineSpaceExtendCoords]`.
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

/- English proof (translation)
Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Simplify using `[he]`. Introduce and unpack `⟨a⟩`. Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord, specToAffineSpaceExtendCoords_appTop_coord_inl]`.
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

/- English proof (translation)
Establish `hsurj : Function.Surjective ⇑(e.appTop)` using `(AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine e).2`. Establish `hproj : specToAffineSpaceExtendCoords k A pA M e σ n b ≫ projLeft k M n = specHomOfGlobalSections A σ ≫ e` using `specToAffineSpaceExtendCoords_comp_projLeft k A pA M e σ n b he`. Establish `hsec : ∀ s : Γ(A, ⊤), ∃ P, (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop P = (Scheme.ΓSpecIso B').inv (σ s)`. Introduce `s`. Take `⟨P, hPs⟩` from `hsurj s`.

Use `⟨(projLeft k M n).appTop P, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun g : Spec B' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)) => g.appTop P) hproj`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h2`. Rewrite using `[h2, hPs, specHomOfGlobalSections_appTop]`. Establish `key : ∀ p : MvPolynomial (Fin n) Γ(A, ⊤), ∃ P, (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop P = (Scheme.ΓSpecIso B').inv (MvPolynomial.eval₂ σ.hom b p)`.

Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C s`. Take `⟨P, hP⟩` from `hsec s`. Use `⟨P, ?_⟩` and prove the remaining obligations.

Rewrite using `[MvPolynomial.eval₂_C]`. Conclude with `hP`. Consider the case `add p q hp hq`. Take `⟨P, hP⟩` from `hp`. Take `⟨Q, hQ⟩` from `hq`.

Use `⟨P + Q, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, MvPolynomial.eval₂_add, map_add, hP, hQ]`. Consider the case `mul_X p j hp`. Take `⟨P, hP⟩` from `hp`. Use `⟨P * AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hP, specToAffineSpaceExtendCoords_appTop_coord_inr, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul]`. Introduce `y`. Take `⟨p, hp⟩` from `hgen ((Scheme.ΓSpecIso B').hom y)`. Take `⟨P, hP⟩` from `key p`. Use `⟨P, ?_⟩` and prove the remaining obligations.

Rewrite using `[hP, hp]`. Simplify using the standard rewrite rules.
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

/- English proof (translation)
The claim follows from `AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine _ (specToAffineSpaceExtendCoords_appTop_surjective k A pA M e σ n b he hgen)`.
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
