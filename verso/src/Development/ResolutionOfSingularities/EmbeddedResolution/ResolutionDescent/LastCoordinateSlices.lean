import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimensionPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceZeroSection
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BasicOpenClosedEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def baseFieldToGlobalSections {X : Scheme.{u}} (k : Type u) [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) : k →+* ↑(X.presheaf.obj (Opposite.op ⊤)) :=
  RingHom.comp (Scheme.Hom.appTop p).hom (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/- English proof (translation)
Use `⟨AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (fun i : ULift.{u, 0} (Fin M ⊕ Fin 1) => Sum.elim (fun b : Fin M => AffineSpace.coord (Spec (CommRingCat.of k)) (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))) (fun j : Fin 1 => AffineSpace.coord …` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `b`. Simplify using `[pullbackCoord_def]`. Simplify using the standard rewrite rules.
-/
private theorem exists_translateLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) :
    ∃ f : affineSpaceTimesLine k M ⟶ affineSpaceTimesLine k M,
      f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) ∧
        (∀ b : Fin M, pullbackCoord f (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) =
          AffineSpace.coord (Spec (CommRingCat.of k))
            (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))) ∧
        (ConcreteCategory.hom (Scheme.Hom.appTop f)) (lastCoordinate k M) =
          lastCoordinate k M +
            baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) a := by
  refine ⟨AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (fun i : ULift.{u, 0} (Fin M ⊕ Fin 1) =>
        Sum.elim
          (fun b : Fin M =>
            AffineSpace.coord (Spec (CommRingCat.of k))
              (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)))
          (fun j : Fin 1 =>
            AffineSpace.coord (Spec (CommRingCat.of k))
                (⟨Sum.inr j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) +
              baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) a)
          i.down),
    ?_, ?_, ?_⟩
  · simp
  · intro b
    simp [pullbackCoord_def]
  · simp

def translateLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) : affineSpaceTimesLine k M ⟶ affineSpaceTimesLine k M :=
  (exists_translateLastCoord k M a).choose

@[simp]
/- English proof (translation)
The claim follows from `(exists_translateLastCoord k M a).choose_spec.1`.
-/
theorem translateLastCoord_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ) (a : k) :
    translateLastCoord k M a ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) :=
  (exists_translateLastCoord k M a).choose_spec.1

/- English proof (translation)
The claim follows from `(exists_translateLastCoord k M a).choose_spec.2.1 b`.
-/
theorem pullbackCoord_translateLastCoord_inl (k : Type u) [Field k] (M : ℕ) (a : k) (b : Fin M) :
    pullbackCoord (translateLastCoord k M a) (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      AffineSpace.coord (Spec (CommRingCat.of k))
        (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) :=
  (exists_translateLastCoord k M a).choose_spec.2.1 b

/- English proof (translation)
The claim follows from `(exists_translateLastCoord k M a).choose_spec.2.2`.
-/
theorem translateLastCoord_appTop_lastCoordinate (k : Type u) [Field k] (M : ℕ) (a : k) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (translateLastCoord k M a))) (lastCoordinate k M) =
      lastCoordinate k M +
        baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) a :=
  (exists_translateLastCoord k M a).choose_spec.2.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem baseFieldToGlobalSections_apply (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (a : k) :
    baseFieldToGlobalSections k p a =
      (ConcreteCategory.hom (Scheme.Hom.appTop p))
        ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of k)).inv) a) :=
  rfl

/- English proof (translation)
Rewrite using `[baseFieldToGlobalSections_apply, baseFieldToGlobalSections_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]`.
-/
private theorem appTop_baseFieldToGlobalSections (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of k)) (a : k) :
    (ConcreteCategory.hom (Scheme.Hom.appTop f)) (baseFieldToGlobalSections k p a) =
      baseFieldToGlobalSections k (f ≫ p) a := by
  rw [baseFieldToGlobalSections_apply, baseFieldToGlobalSections_apply, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

/- English proof (translation)
The claim follows from `map_neg (baseFieldToGlobalSections k p) a`.
-/
private theorem baseFieldToGlobalSections_neg (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (a : k) :
    baseFieldToGlobalSections k p (-a) = -baseFieldToGlobalSections k p a :=
  map_neg (baseFieldToGlobalSections k p) a

/- English proof (translation)
Establish `hstruct : ∀ b : k, translateLastCoord k M b ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) = affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))` using `translateLastCoord_comp_affineSpaceIndexedByToSpec k M`. Establish `hconst : ∀ b c : k, (ConcreteCategory.hom (Scheme.Hom.appTop (translateLastCoord k M b))) (baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) c) = baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) c`. Introduce `b c`. Rewrite using `[appTop_baseFieldToGlobalSections, hstruct b]`. Establish `H0 : (translateLastCoord k M a ≫ translateLastCoord k M (-a)) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) = 𝟙 (affineSpaceTimesLine k M) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))`.

Rewrite using `[Category.assoc, hstruct, hstruct, Category.id_comp]`. Establish `H : ∀ i : ULift.{u, 0} (Fin M ⊕ Fin 1), (ConcreteCategory.hom (Scheme.Hom.appTop (translateLastCoord k M a ≫ translateLastCoord k M (-a)))) (AffineSpace.coord (Spec (CommRingCat.of k)) i) = (ConcreteCategory.hom (Scheme.Hom.appTop (𝟙 (affineSpaceTimesLine k M)))) (AffineSpace.coo …`. Introduce and unpack `⟨b | j⟩`. Establish `h1` using `pullbackCoord_translateLastCoord_inl k M a b`. Establish `h2` using `pullbackCoord_translateLastCoord_inl k M (-a) b`.

Rewrite `h1`, `h2` using `[pullbackCoord_def]`. Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h2, h1, Scheme.Hom.id_appTop, CommRingCat.id_apply]`. Establish `h1` using `translateLastCoord_appTop_lastCoordinate k M a`. Establish `h2` using `translateLastCoord_appTop_lastCoordinate k M (-a)`. Rewrite using `[← lastCoordinate_eq_coord k M j, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h2, map_add, h1, hconst, map_neg, Scheme.Hom.id_appTop, CommRingCat.id_apply, add_neg_cancel_right]`.

Apply `AffineSpace.hom_ext` to reduce the goal to its premises. Conclude with `H0`. Conclude with `H`.
-/
theorem translateLastCoord_comp_translateLastCoord_neg (k : Type u) [Field k] (M : ℕ) (a : k) :
    translateLastCoord k M a ≫ translateLastCoord k M (-a) = 𝟙 (affineSpaceTimesLine k M) := by
  have hstruct : ∀ b : k,
      translateLastCoord k M b ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := translateLastCoord_comp_affineSpaceIndexedByToSpec k M
  have hconst : ∀ b c : k,
      (ConcreteCategory.hom (Scheme.Hom.appTop (translateLastCoord k M b)))
          (baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) c) =
        baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) c := by
    intro b c
    rw [appTop_baseFieldToGlobalSections, hstruct b]
  have H0 : (translateLastCoord k M a ≫ translateLastCoord k M (-a)) ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      𝟙 (affineSpaceTimesLine k M) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
    rw [Category.assoc, hstruct, hstruct, Category.id_comp]
  have H : ∀ i : ULift.{u, 0} (Fin M ⊕ Fin 1),
      (ConcreteCategory.hom (Scheme.Hom.appTop (translateLastCoord k M a ≫ translateLastCoord k M (-a))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
        (ConcreteCategory.hom (Scheme.Hom.appTop (𝟙 (affineSpaceTimesLine k M))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) i) := by
    rintro ⟨b | j⟩
    · have h1 := pullbackCoord_translateLastCoord_inl k M a b
      have h2 := pullbackCoord_translateLastCoord_inl k M (-a) b
      rw [pullbackCoord_def] at h1 h2
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h2, h1, Scheme.Hom.id_appTop,
        CommRingCat.id_apply]
    · have h1 := translateLastCoord_appTop_lastCoordinate k M a
      have h2 := translateLastCoord_appTop_lastCoordinate k M (-a)
      rw [← lastCoordinate_eq_coord k M j, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h2,
        map_add, h1, hconst, map_neg, Scheme.Hom.id_appTop, CommRingCat.id_apply,
        add_neg_cancel_right]
  apply AffineSpace.hom_ext
  · exact H0
  · exact H

/- English proof (translation)
Establish `h` using `translateLastCoord_comp_translateLastCoord_neg k M (-a)`. Rewrite `h` using `[neg_neg]`. Then use the resulting hypothesis.
-/
theorem translateLastCoord_neg_comp_translateLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) :
    translateLastCoord k M (-a) ≫ translateLastCoord k M a = 𝟙 (affineSpaceTimesLine k M) := by
  have h := translateLastCoord_comp_translateLastCoord_neg k M (-a)
  rwa [neg_neg] at h

def translateLastCoordIso (k : Type u) [Field k] (M : ℕ) (a : k) : affineSpaceTimesLine k M ≅ affineSpaceTimesLine k M where
  hom := translateLastCoord k M a
  inv := translateLastCoord k M (-a)
  hom_inv_id := translateLastCoord_comp_translateLastCoord_neg k M a
  inv_hom_id := translateLastCoord_neg_comp_translateLastCoord k M a

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem translateLastCoordIso_hom (k : Type u) [Field k] (M : ℕ) (a : k) :
    (translateLastCoordIso k M a).hom = translateLastCoord k M a := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem translateLastCoordIso_inv (k : Type u) [Field k] (M : ℕ) (a : k) :
    (translateLastCoordIso k M a).inv = translateLastCoord k M (-a) := rfl

/- English proof (translation)
Use `⟨AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (fun i : ULift.{u, 0} (Fin M ⊕ Fin 1) => Sum.elim (fun b : Fin M => AffineSpace.coord (Spec (CommRingCat.of k)) (⟨b⟩ : ULift.{u, 0} (Fin M))) (fun _ : Fin 1 => baseFieldToGlobalSections k (affineSpaceI …` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `isClosedImmersion_of_coord_surjective _ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce and unpack `⟨b⟩`.

Conclude with `⟨AffineSpace.coord (Spec (CommRingCat.of k)) (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)), by simp⟩`. Apply `AffineSpace.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨b⟩`.

Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
private theorem exists_sliceAtLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) :
    ∃ f : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶ affineSpaceTimesLine k M,
      f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) ∧
        IsClosedImmersion f ∧
        f ≫ projLeft k M 1 = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) ∧
        (ConcreteCategory.hom (Scheme.Hom.appTop f)) (lastCoordinate k M) =
          baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) a := by
  refine ⟨AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
      (fun i : ULift.{u, 0} (Fin M ⊕ Fin 1) =>
        Sum.elim
          (fun b : Fin M =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (⟨b⟩ : ULift.{u, 0} (Fin M)))
          (fun _ : Fin 1 =>
            baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) a)
          i.down),
    ?_, ?_, ?_, ?_⟩
  · simp
  · refine isClosedImmersion_of_coord_surjective _ ?_ ?_
    · simp
    · rintro ⟨b⟩
      exact ⟨AffineSpace.coord (Spec (CommRingCat.of k))
        (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)), by simp⟩
  · apply AffineSpace.hom_ext
    · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec]
      simp
    · rintro ⟨b⟩
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord]
      simp
  · simp

def sliceAtLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) :
    affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶ affineSpaceTimesLine k M :=
  (exists_sliceAtLastCoord k M a).choose

@[simp]
/- English proof (translation)
The claim follows from `(exists_sliceAtLastCoord k M a).choose_spec.1`.
-/
theorem sliceAtLastCoord_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ) (a : k) :
    sliceAtLastCoord k M a ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) :=
  (exists_sliceAtLastCoord k M a).choose_spec.1

/- English proof (translation)
The claim follows from `(exists_sliceAtLastCoord k M a).choose_spec.2.1`.
-/
theorem isClosedImmersion_sliceAtLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) :
    IsClosedImmersion (sliceAtLastCoord k M a) :=
  (exists_sliceAtLastCoord k M a).choose_spec.2.1

instance instIsClosedImmersionHeightSlice (k : Type u) [Field k] (M : ℕ) (a : k) :
    IsClosedImmersion (sliceAtLastCoord k M a) :=
  isClosedImmersion_sliceAtLastCoord k M a

@[simp]
/- English proof (translation)
The claim follows from `(exists_sliceAtLastCoord k M a).choose_spec.2.2.1 @[simp]`.
-/
theorem sliceAtLastCoord_comp_projLeft (k : Type u) [Field k] (M : ℕ) (a : k) :
    sliceAtLastCoord k M a ≫ projLeft k M 1 = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) :=
  (exists_sliceAtLastCoord k M a).choose_spec.2.2.1

@[simp]
/- English proof (translation)
Rewrite using `[← Category.assoc, sliceAtLastCoord_comp_projLeft, Category.id_comp]`.
-/
theorem sliceAtLastCoord_comp_projLeft_assoc (k : Type u) [Field k] (M : ℕ) (a : k) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶ Z) :
    sliceAtLastCoord k M a ≫ projLeft k M 1 ≫ g = g := by
  rw [← Category.assoc, sliceAtLastCoord_comp_projLeft, Category.id_comp]

/- English proof (translation)
The claim follows from `(exists_sliceAtLastCoord k M a).choose_spec.2.2.2`.
-/
theorem sliceAtLastCoord_appTop_lastCoordinate (k : Type u) [Field k] (M : ℕ) (a : k) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M a))) (lastCoordinate k M) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) a :=
  (exists_sliceAtLastCoord k M a).choose_spec.2.2.2

def sliceSeparatingFunction (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → k) (i : ι) : ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)) :=
  ∏ j ∈ Finset.univ.erase i,
    (lastCoordinate k M -
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (e j))

def sliceSeparatingOpen (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → k) (i : ι) : (affineSpaceTimesLine k M).Opens :=
  (affineSpaceTimesLine k M).basicOpen (sliceSeparatingFunction k M e i)

def coproductSliceMap (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) : (∐ A) ⟶ affineSpaceTimesLine k M :=
  Sigma.desc fun i => ρ i ≫ sliceAtLastCoord k M (e i)

@[simp]
/- English proof (translation)
Simplify using `[coproductSliceMap]`. Use the proof step `@[simp]`.
-/
theorem sigma_ι_coproductSliceMap (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    Sigma.ι A i ≫ coproductSliceMap k M e A ρ = ρ i ≫ sliceAtLastCoord k M (e i) := by
  simp [coproductSliceMap]

@[simp]
/- English proof (translation)
Rewrite using `[← Category.assoc, sigma_ι_coproductSliceMap, Category.assoc]`.
-/
theorem sigma_ι_coproductSliceMap_assoc (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k)
    (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι)
    {Z : Scheme.{u}} (g : affineSpaceTimesLine k M ⟶ Z) :
    Sigma.ι A i ≫ coproductSliceMap k M e A ρ ≫ g = ρ i ≫ sliceAtLastCoord k M (e i) ≫ g := by
  rw [← Category.assoc, sigma_ι_coproductSliceMap, Category.assoc]

/- English proof (translation)
Establish `hp : pullbackAlongProjection k M G = (ConcreteCategory.hom (Scheme.Hom.appTop (projLeft k M 1))) G` using `rfl`. Rewrite using `[hp, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, sliceAtLastCoord_comp_projLeft, Scheme.Hom.id_appTop, CommRingCat.id_apply]`.
-/
private theorem sliceAtLastCoord_appTop_pullbackAlongProjection (k : Type u) [Field k] (M : ℕ) (a : k)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M a))) (pullbackAlongProjection k M G) = G := by
  have hp : pullbackAlongProjection k M G =
      (ConcreteCategory.hom (Scheme.Hom.appTop (projLeft k M 1))) G := rfl
  rw [hp, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, sliceAtLastCoord_comp_projLeft,
    Scheme.Hom.id_appTop, CommRingCat.id_apply]

/- English proof (translation)
Rewrite using `[appTop_baseFieldToGlobalSections, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]`.
-/
private theorem sliceAtLastCoord_appTop_baseFieldToGlobalSections (k : Type u) [Field k] (M : ℕ) (a x : k) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M a)))
        (baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) x) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) x := by
  rw [appTop_baseFieldToGlobalSections, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]

private def lagrangeBasisSection (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (j : ι) : ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)) :=
  baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      ((∏ l ∈ Finset.univ.erase j, (e j - e l))⁻¹) *
    ∏ l ∈ Finset.univ.erase j,
      (lastCoordinate k M -
        baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (e l))

/- English proof (translation)
Establish `hlag : lagrangeBasisSection k M e j = baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) ((∏ l ∈ Finset.univ.erase j, (e j - e l))⁻¹) * ∏ l ∈ Finset.univ.erase j, (lastCoordinate k M - baseFieldToGlobalSections k (affineSpaceIndexedByToSpec …` using `rfl`. Rewrite using `[hlag, map_mul, map_prod]`. Simplify using `only [map_sub, sliceAtLastCoord_appTop_baseFieldToGlobalSections, sliceAtLastCoord_appTop_lastCoordinate]`. Establish `hprod : (∏ l ∈ Finset.univ.erase j, (baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (e i) - baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (e l))) = baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (UL …`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_congr rfl fun l _ => (map_sub _ _ _).symm`. Rewrite using `[hprod, ← map_mul]`. Distinguish the cases in `hji : j = i`. Rewrite using `[if_pos hji, ← hji]`. Establish `hne : (∏ l ∈ Finset.univ.erase j, (e j - e l)) ≠ 0`.

Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `l hl`. Conclude with `sub_ne_zero_of_ne fun hcon => (Finset.mem_erase.mp hl).1 (he hcon).symm`. Rewrite using `[inv_mul_cancel₀ hne, map_one]`. Establish `hz : (∏ l ∈ Finset.univ.erase j, (e i - e l)) = 0` using `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun hc => hji hc.symm, Finset.mem_univ i⟩) (sub_self (e i))`.

Rewrite using `[if_neg hji, hz, mul_zero, map_zero]`.
-/
private theorem sliceAtLastCoord_appTop_lagrangeSection (k : Type u) [Field k] (M : ℕ) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (i j : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M (e i))))
        (lagrangeBasisSection k M e j) = if j = i then 1 else 0 := by
  have hlag : lagrangeBasisSection k M e j =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
          ((∏ l ∈ Finset.univ.erase j, (e j - e l))⁻¹) *
        ∏ l ∈ Finset.univ.erase j,
          (lastCoordinate k M -
            baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
              (e l)) := rfl
  rw [hlag, map_mul, map_prod]
  simp only [map_sub, sliceAtLastCoord_appTop_baseFieldToGlobalSections, sliceAtLastCoord_appTop_lastCoordinate]
  have hprod : (∏ l ∈ Finset.univ.erase j,
        (baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (e i) -
          baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (e l))) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
        (∏ l ∈ Finset.univ.erase j, (e i - e l)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun l _ => (map_sub _ _ _).symm
  rw [hprod, ← map_mul]
  by_cases hji : j = i
  · rw [if_pos hji, ← hji]
    have hne : (∏ l ∈ Finset.univ.erase j, (e j - e l)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro l hl
      exact sub_ne_zero_of_ne fun hcon => (Finset.mem_erase.mp hl).1 (he hcon).symm
    rw [inv_mul_cancel₀ hne, map_one]
  · have hz : (∏ l ∈ Finset.univ.erase j, (e i - e l)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun hc => hji hc.symm, Finset.mem_univ i⟩)
        (sub_self (e i))
    rw [if_neg hji, hz, mul_zero, map_zero]

/- English proof (translation)
Rewrite using `[map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]`. Simplify using `only [map_mul, sliceAtLastCoord_appTop_pullbackAlongProjection, sliceAtLastCoord_appTop_lagrangeSection k M e he i i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `only [map_mul, sliceAtLastCoord_appTop_lagrangeSection k M e he i j]`.

Rewrite using `[if_neg hj, mul_zero]`.
-/
private theorem sliceAtLastCoord_appTop_sum_mul_lagrangeSection (k : Type u) [Field k] (M : ℕ) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Function.Injective e)
    (G : ι → ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) (i : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M (e i))))
        (∑ j : ι, pullbackAlongProjection k M (G j) * lagrangeBasisSection k M e j) = G i := by
  rw [map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp only [map_mul, sliceAtLastCoord_appTop_pullbackAlongProjection,
      sliceAtLastCoord_appTop_lagrangeSection k M e he i i]
    simp
  · intro j _ hj
    simp only [map_mul, sliceAtLastCoord_appTop_lagrangeSection k M e he i j]
    rw [if_neg hj, mul_zero]

/- English proof (translation)
Establish `hv : ∀ (v : ↑((∐ A).presheaf.obj (Opposite.op ⊤))) (c : ULift.{u, 0} (Fin 1)), (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => v)))) (AffineSpace.coord (Spec (CommRingCat.of k)) c) = v`. Introduce `v c`. Simplify using the standard rewrite rules. Establish `hfg : AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => s) = AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => t)`. Use `Limits.Sigma.hom_ext _ _ fun i => ?_` and prove the remaining obligations.

Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `c`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]`. Rewrite using `[hv s c, hv t c]`.

Conclude with `h i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hfg]`. Use `_ = t := hv t ⟨0⟩`.
-/
private theorem coproduct_globalSections_ext (k : Type u) [Field k] {ι : Type u} (A : ι → Scheme.{u})
    (q : (∐ A) ⟶ Spec (CommRingCat.of k))
    (s t : ↑((∐ A).presheaf.obj (Opposite.op ⊤)))
    (h : ∀ i : ι, (ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A i))) s =
      (ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A i))) t) : s = t := by
  have hv : ∀ (v : ↑((∐ A).presheaf.obj (Opposite.op ⊤))) (c : ULift.{u, 0} (Fin 1)),
      (ConcreteCategory.hom (Scheme.Hom.appTop
        (AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => v))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) c) = v := by
    intro v c
    simp
  have hfg : AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => s) =
      AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => t) := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro c
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rw [hv s c, hv t c]
      exact h i
  calc s = (ConcreteCategory.hom (Scheme.Hom.appTop
        (AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => s))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨0⟩ : ULift.{u, 0} (Fin 1))) :=
        (hv s ⟨0⟩).symm
    _ = (ConcreteCategory.hom (Scheme.Hom.appTop
        (AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => t))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨0⟩ : ULift.{u, 0} (Fin 1))) := by
        rw [hfg]
    _ = t := hv t ⟨0⟩

/- English proof (translation)
Establish `haffine : IsAffine (∐ A)` using `inferInstance`. Establish `hsurj : ∀ F : ↑((∐ A).presheaf.obj (Opposite.op ⊤)), ∃ H : ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)), (ConcreteCategory.hom (Scheme.Hom.appTop (coproductSliceMap k M e A ρ))) H = F`. Introduce `F`. Use `⟨∑ j : ι, pullbackAlongProjection k M (globalSectionLift k M (ρ j) ((ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A j))) F)) * lagrangeBasisSection k M e j, ?_⟩` and prove the remaining obligations. Use `coproduct_globalSections_ext k A (Sigma.desc fun j => ρ j ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) _ _ fun i => ?_` and prove the remaining obligations.

Rewrite using `[← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, sigma_ι_coproductSliceMap, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, sliceAtLastCoord_appTop_sum_mul_lagrangeSection k M e he (fun j => globalSectionLift k M (ρ j) ((ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A j))) …`. Conclude with `IsClosedImmersion.of_surjective_of_isAffine (coproductSliceMap k M e A ρ) hsurj`.
-/
theorem isClosedImmersion_coproductSliceMap (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    [∀ i, IsAffine (A i)] (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    [∀ i, IsClosedImmersion (ρ i)] : IsClosedImmersion (coproductSliceMap k M e A ρ) := by
  have haffine : IsAffine (∐ A) := inferInstance
  have hsurj : ∀ F : ↑((∐ A).presheaf.obj (Opposite.op ⊤)),
      ∃ H : ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)),
        (ConcreteCategory.hom (Scheme.Hom.appTop (coproductSliceMap k M e A ρ))) H = F := by
    intro F
    refine ⟨∑ j : ι, pullbackAlongProjection k M (globalSectionLift k M (ρ j)
        ((ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A j))) F)) *
          lagrangeBasisSection k M e j, ?_⟩
    refine coproduct_globalSections_ext k A
      (Sigma.desc fun j => ρ j ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) _ _ fun i => ?_
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, sigma_ι_coproductSliceMap, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply,
      sliceAtLastCoord_appTop_sum_mul_lagrangeSection k M e he
        (fun j => globalSectionLift k M (ρ j)
          ((ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A j))) F)) i,
      appTop_globalSectionLift]
  exact IsClosedImmersion.of_surjective_of_isAffine (coproductSliceMap k M e A ρ) hsurj

/- English proof (translation)
Use `CategoryTheory.Limits.Sigma.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[sigma_ι_coproductSliceMap_assoc, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec, hq i]`.
-/
theorem coproductSliceMap_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k)
    (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    (q : (∐ A) ⟶ Spec (CommRingCat.of k))
    (hq : ∀ i, Sigma.ι A i ≫ q = ρ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) :
    coproductSliceMap k M e A ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) = q := by
  refine CategoryTheory.Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [sigma_ι_coproductSliceMap_assoc, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec, hq i]

/- English proof (translation)
Take `⟨⟨i, y⟩, rfl⟩` from `(sigmaMk A).surjective x`. Conclude with `⟨i, y, (sigmaMk_mk A i y).symm⟩`.
-/
private theorem sigma_ι_base_jointly_surjective {ι : Type u} (A : ι → Scheme.{u}) (x : ↥(∐ A)) :
    ∃ (j : ι) (b : ↥(A j)), (Sigma.ι A j).base b = x := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk A).surjective x
  exact ⟨i, y, (sigmaMk_mk A i y).symm⟩

/- English proof (translation)
Use `show (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base b = (ρ j ≫ sliceAtLastCoord k M (e j)).base b`. Rewrite using `[sigma_ι_coproductSliceMap]`.
-/
private theorem coproductSliceMap_base_sigma_ι (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k)
    (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (j : ι)
    (b : ↥(A j)) :
    (coproductSliceMap k M e A ρ).base ((Sigma.ι A j).base b) =
      (ρ j ≫ sliceAtLastCoord k M (e j)).base b := by
  show (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base b = (ρ j ≫ sliceAtLastCoord k M (e j)).base b
  rw [sigma_ι_coproductSliceMap]

/- English proof (translation)
Establish `hdef : sliceSeparatingFunction k M e i = ∏ l ∈ Finset.univ.erase i, (lastCoordinate k M - baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (e l))` using `rfl`. Rewrite using `[hdef, map_prod, map_prod]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, sliceAtLastCoord_appTop_lastCoordinate, appTop_baseFieldToGlobalSections, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]`.
-/
private theorem sliceAtLastCoord_appTop_sliceSeparatingFunction_eq_prod_sub (k : Type u) [Field k] (M : ℕ) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : ι → k) (i j : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M (e j)))) (sliceSeparatingFunction k M e i) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
        (∏ l ∈ Finset.univ.erase i, (e j - e l)) := by
  have hdef : sliceSeparatingFunction k M e i =
      ∏ l ∈ Finset.univ.erase i,
        (lastCoordinate k M -
          baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (e l)) := rfl
  rw [hdef, map_prod, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [map_sub, map_sub, sliceAtLastCoord_appTop_lastCoordinate, appTop_baseFieldToGlobalSections,
    sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]

/- English proof (translation)
Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.comp_apply, sliceAtLastCoord_appTop_sliceSeparatingFunction_eq_prod_sub, appTop_baseFieldToGlobalSections]`.
-/
private theorem comp_sliceAtLastCoord_appTop_sliceSeparatingFunction (k : Type u) [Field k] (M : ℕ) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i j : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (ρ j ≫ sliceAtLastCoord k M (e j))))
        (sliceSeparatingFunction k M e i) =
      baseFieldToGlobalSections k (ρ j ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
        (∏ l ∈ Finset.univ.erase i, (e j - e l)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, sliceAtLastCoord_appTop_sliceSeparatingFunction_eq_prod_sub,
    appTop_baseFieldToGlobalSections]

/- English proof (translation)
Establish `hne0 : (∏ l ∈ Finset.univ.erase i, (e i - e l)) ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `l hl`. Conclude with `sub_ne_zero.2 fun hx => (Finset.mem_erase.1 hl).1 (he hx).symm`. Establish `hunit : IsUnit ((ConcreteCategory.hom (Scheme.Hom.appTop (ρ i ≫ sliceAtLastCoord k M (e i)))) (sliceSeparatingFunction k M e i))`.

Rewrite using `[comp_sliceAtLastCoord_appTop_sliceSeparatingFunction]`. Conclude with `IsUnit.map _ (isUnit_iff_ne_zero.2 hne0)`. Establish `hbasic : (Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj (sliceSeparatingOpen k M e i) = (A i).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop (ρ i ≫ sliceAtLastCoord k M (e i)))) (sliceSeparatingFunction k M e i))` using `Scheme.preimage_basicOpen _ _`. Establish `hpre : (Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj (sliceSeparatingOpen k M e i) = ⊤`. Rewrite using `[hbasic]`.

Conclude with `(A i).basicOpen_of_isUnit hunit`. Establish `hmem : b ∈ (Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj (sliceSeparatingOpen k M e i)`. Rewrite using `[hpre]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `hmem`.
-/
private theorem mem_sliceSeparatingOpen (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) (b : ↥(A i)) :
    (ρ i ≫ sliceAtLastCoord k M (e i)).base b ∈ sliceSeparatingOpen k M e i := by
  have hne0 : (∏ l ∈ Finset.univ.erase i, (e i - e l)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    exact sub_ne_zero.2 fun hx => (Finset.mem_erase.1 hl).1 (he hx).symm
  have hunit : IsUnit ((ConcreteCategory.hom (Scheme.Hom.appTop (ρ i ≫ sliceAtLastCoord k M (e i))))
      (sliceSeparatingFunction k M e i)) := by
    rw [comp_sliceAtLastCoord_appTop_sliceSeparatingFunction]
    exact IsUnit.map _ (isUnit_iff_ne_zero.2 hne0)
  have hbasic : (Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj (sliceSeparatingOpen k M e i) =
      (A i).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop
        (ρ i ≫ sliceAtLastCoord k M (e i)))) (sliceSeparatingFunction k M e i)) :=
    Scheme.preimage_basicOpen _ _
  have hpre : (Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj (sliceSeparatingOpen k M e i) = ⊤ := by
    rw [hbasic]
    exact (A i).basicOpen_of_isUnit hunit
  have hmem : b ∈ (Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj (sliceSeparatingOpen k M e i) := by
    rw [hpre]; trivial
  exact hmem

/- English proof (translation)
Establish `hzero : (∏ l ∈ Finset.univ.erase i, (e j - e l)) = 0` using `Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, Finset.mem_univ j⟩) (sub_self _)`. Establish `hbasic : (Opens.map (ρ j ≫ sliceAtLastCoord k M (e j)).base).obj (sliceSeparatingOpen k M e i) = (A j).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop (ρ j ≫ sliceAtLastCoord k M (e j)))) (sliceSeparatingFunction k M e i))` using `Scheme.preimage_basicOpen _ _`. Establish `hpre : (Opens.map (ρ j ≫ sliceAtLastCoord k M (e j)).base).obj (sliceSeparatingOpen k M e i) = ⊥`. Rewrite using `[hbasic, comp_sliceAtLastCoord_appTop_sliceSeparatingFunction, hzero, map_zero, Scheme.basicOpen_zero]`. Introduce `hmem`.

Establish `hmem' : b ∈ (Opens.map (ρ j ≫ sliceAtLastCoord k M (e j)).base).obj (sliceSeparatingOpen k M e i)` using `hmem`. Rewrite `hmem'` using `[hpre]`. Simplify using `at hmem'`.
-/
private theorem not_mem_sliceSeparatingOpen_of_ne (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i j : ι) (hne : j ≠ i)
    (b : ↥(A j)) :
    (ρ j ≫ sliceAtLastCoord k M (e j)).base b ∉ sliceSeparatingOpen k M e i := by
  have hzero : (∏ l ∈ Finset.univ.erase i, (e j - e l)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, Finset.mem_univ j⟩) (sub_self _)
  have hbasic : (Opens.map (ρ j ≫ sliceAtLastCoord k M (e j)).base).obj (sliceSeparatingOpen k M e i) =
      (A j).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop
        (ρ j ≫ sliceAtLastCoord k M (e j)))) (sliceSeparatingFunction k M e i)) :=
    Scheme.preimage_basicOpen _ _
  have hpre : (Opens.map (ρ j ≫ sliceAtLastCoord k M (e j)).base).obj (sliceSeparatingOpen k M e i) = ⊥ := by
    rw [hbasic, comp_sliceAtLastCoord_appTop_sliceSeparatingFunction, hzero, map_zero, Scheme.basicOpen_zero]
  intro hmem
  have hmem' : b ∈ (Opens.map (ρ j ≫ sliceAtLastCoord k M (e j)).base).obj (sliceSeparatingOpen k M e i) :=
    hmem
  rw [hpre] at hmem'
  simp at hmem'

/- English proof (translation)
Establish `hqcj : ∀ j, QuasiCompact (ρ j ≫ sliceAtLastCoord k M (e j))` using `fun j => inferInstance`. Use `⟨fun V hV1 hV2 => ?_⟩` and prove the remaining obligations. Establish `hset : ⇑(coproductSliceMap k M e A ρ).base ⁻¹' V = ⋃ j, ⇑(Sigma.ι A j).base '' (⇑(ρ j ≫ sliceAtLastCoord k M (e j)).base ⁻¹' V)`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨j, b, rfl⟩` from `sigma_ι_base_jointly_surjective A y`. Use `Set.mem_iUnion.2 ⟨j, b, ?_, rfl⟩` and prove the remaining obligations. Use `show (ρ j ≫ sliceAtLastCoord k M (e j)).base b ∈ V`. Rewrite using `[← coproductSliceMap_base_sigma_ι k M e A ρ j b]`. Conclude with `hy`.

Introduce `y hy`. Take `⟨j, hj⟩` from `Set.mem_iUnion.1 hy`. Take `⟨b, hb, rfl⟩` from `hj`. Use `show (coproductSliceMap k M e A ρ).base ((Sigma.ι A j).base b) ∈ V`. Rewrite using `[coproductSliceMap_base_sigma_ι]`.

Conclude with `hb`. Rewrite using `[hset]`. Use `isCompact_iUnion fun j => ?_` and prove the remaining obligations. Conclude with `(QuasiCompact.isCompact_preimage (f := ρ j ≫ sliceAtLastCoord k M (e j)) V hV1 hV2).image (Sigma.ι A j).continuous`.
-/
private theorem quasiCompact_coproductSliceMap (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [∀ i, IsClosedImmersion (ρ i)] :
    QuasiCompact (coproductSliceMap k M e A ρ) := by
  have hqcj : ∀ j, QuasiCompact (ρ j ≫ sliceAtLastCoord k M (e j)) := fun j => inferInstance
  refine ⟨fun V hV1 hV2 => ?_⟩
  have hset : ⇑(coproductSliceMap k M e A ρ).base ⁻¹' V =
      ⋃ j, ⇑(Sigma.ι A j).base '' (⇑(ρ j ≫ sliceAtLastCoord k M (e j)).base ⁻¹' V) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨j, b, rfl⟩ := sigma_ι_base_jointly_surjective A y
      refine Set.mem_iUnion.2 ⟨j, b, ?_, rfl⟩
      show (ρ j ≫ sliceAtLastCoord k M (e j)).base b ∈ V
      rw [← coproductSliceMap_base_sigma_ι k M e A ρ j b]
      exact hy
    · intro y hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
      obtain ⟨b, hb, rfl⟩ := hj
      show (coproductSliceMap k M e A ρ).base ((Sigma.ι A j).base b) ∈ V
      rw [coproductSliceMap_base_sigma_ι]
      exact hb
  rw [hset]
  refine isCompact_iUnion fun j => ?_
  exact (QuasiCompact.isCompact_preimage (f := ρ j ≫ sliceAtLastCoord k M (e j)) V hV1 hV2).image
    (Sigma.ι A j).continuous

/- English proof (translation)
Establish `: QuasiCompact (coproductSliceMap k M e A ρ)` using `quasiCompact_coproductSliceMap k M e A ρ`. Establish `: QuasiCompact (ρ i ≫ sliceAtLastCoord k M (e i))` using `inferInstance`. Establish `hfun : ⇑(Scheme.Opens.ι (X` using `A i) ((Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj U) ≫ Sigma.ι A i).base = ⇑(Sigma.ι A i).base ∘ ⇑(Scheme.Opens.ι (X := A i) ((Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj U)).base :=`. Use function extensionality and compare the values at `fun _ => rfl`. Establish `hrange : Set.range ⇑(Scheme.Opens.ι (X` using `A i) ((Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj U) ≫ Sigma.ι A i).base = Set.range ⇑(Scheme.Opens.ι (X := ∐ A) ((Opens.map (coproductSliceMap k M e A ρ).base).obj U)).base := by`.

Rewrite using `[hfun, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]`. Use `show ⇑(Sigma.ι A i).base '' (⇑(ρ i ≫ sliceAtLastCoord k M (e i)).base ⁻¹' (U : Set ↥(affineSpaceTimesLine k M))) = ⇑(coproductSliceMap k M e A ρ).base ⁻¹' (U : Set ↥(affineSpaceTimesLine k M))`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨b, hb, rfl⟩ show (coproductSliceMap k M e A ρ).base ((Sigma.ι A i).base b) ∈ (U : Set ↥(affineSpaceTimesLine k M))`. Rewrite using `[coproductSliceMap_base_sigma_ι]`.

Conclude with `hb`. Introduce `y hy`. Take `⟨j, b, rfl⟩` from `sigma_ι_base_jointly_surjective A y`. Establish `hb : (ρ j ≫ sliceAtLastCoord k M (e j)).base b ∈ (U : Set ↥(affineSpaceTimesLine k M))`. Establish `hy' : (coproductSliceMap k M e A ρ).base ((Sigma.ι A j).base b) ∈ (U : Set ↥(affineSpaceTimesLine k M))` using `hy`.

Rewrite `hy'` using `[coproductSliceMap_base_sigma_ι]`. Then use the resulting hypothesis. Break down `eq_or_ne j i with rfl | hne` into its components or cases. Conclude with `⟨b, hb, rfl⟩`. Conclude with `absurd (hU hb) (not_mem_sliceSeparatingOpen_of_ne k M e A ρ i j hne b)`. Use `(ker_comap_ι_eq_ker_of_isIso_comp (coproductSliceMap k M e A ρ) U ((ρ i ≫ sliceAtLastCoord k M (e i)) ∣_ U) (IsOpenImmersion.isoOfRangeEq _ _ hrange).hom ?_).trans (ker_comap_ι_eq_ker_morphismRestrict (ρ i ≫ sliceAtLastCoord k M (e i)) U).symm` and prove the remaining obligations.

Rewrite using `[← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc, sigma_ι_coproductSliceMap, morphismRestrict_ι]`.
-/
private theorem comap_ker_coproductSliceMap_eq_of_le_sliceSeparatingOpen (k : Type u) [Field k] (M : ℕ) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [∀ i, IsClosedImmersion (ρ i)]
    (i : ι) (U : (affineSpaceTimesLine k M).Opens) (hU : U ≤ sliceSeparatingOpen k M e i) :
    (Scheme.Hom.ker (coproductSliceMap k M e A ρ)).comap U.ι =
      (Scheme.Hom.ker (ρ i ≫ sliceAtLastCoord k M (e i))).comap U.ι := by
  have : QuasiCompact (coproductSliceMap k M e A ρ) := quasiCompact_coproductSliceMap k M e A ρ
  have : QuasiCompact (ρ i ≫ sliceAtLastCoord k M (e i)) := inferInstance
  have hfun : ⇑(Scheme.Opens.ι (X := A i)
        ((Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj U) ≫ Sigma.ι A i).base =
      ⇑(Sigma.ι A i).base ∘
        ⇑(Scheme.Opens.ι (X := A i)
          ((Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj U)).base :=
    funext fun _ => rfl
  have hrange :
      Set.range ⇑(Scheme.Opens.ι (X := A i)
          ((Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj U) ≫ Sigma.ι A i).base =
        Set.range ⇑(Scheme.Opens.ι (X := ∐ A)
          ((Opens.map (coproductSliceMap k M e A ρ).base).obj U)).base := by
    rw [hfun, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    show ⇑(Sigma.ι A i).base '' (⇑(ρ i ≫ sliceAtLastCoord k M (e i)).base ⁻¹'
        (U : Set ↥(affineSpaceTimesLine k M))) =
      ⇑(coproductSliceMap k M e A ρ).base ⁻¹' (U : Set ↥(affineSpaceTimesLine k M))
    apply Set.Subset.antisymm
    · rintro _ ⟨b, hb, rfl⟩
      show (coproductSliceMap k M e A ρ).base ((Sigma.ι A i).base b) ∈ (U : Set ↥(affineSpaceTimesLine k M))
      rw [coproductSliceMap_base_sigma_ι]
      exact hb
    · intro y hy
      obtain ⟨j, b, rfl⟩ := sigma_ι_base_jointly_surjective A y
      have hb : (ρ j ≫ sliceAtLastCoord k M (e j)).base b ∈ (U : Set ↥(affineSpaceTimesLine k M)) := by
        have hy' : (coproductSliceMap k M e A ρ).base ((Sigma.ι A j).base b) ∈
            (U : Set ↥(affineSpaceTimesLine k M)) := hy
        rwa [coproductSliceMap_base_sigma_ι] at hy'
      rcases eq_or_ne j i with rfl | hne
      · exact ⟨b, hb, rfl⟩
      · exact absurd (hU hb) (not_mem_sliceSeparatingOpen_of_ne k M e A ρ i j hne b)
  refine (ker_comap_ι_eq_ker_of_isIso_comp (coproductSliceMap k M e A ρ) U
      ((ρ i ≫ sliceAtLastCoord k M (e i)) ∣_ U)
      (IsOpenImmersion.isoOfRangeEq _ _ hrange).hom ?_).trans
    (ker_comap_ι_eq_ker_morphismRestrict (ρ i ≫ sliceAtLastCoord k M (e i)) U).symm
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc, sigma_ι_coproductSliceMap, morphismRestrict_ι]

/- English proof (translation)
Apply `AffineSpace.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, translateLastCoord_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]`. Introduce and unpack `⟨b | j⟩`. Establish `h0` using `sliceAtLastCoord_comp_projLeft k M a`. Establish `h1` using `congrArg (fun m : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) => (ConcreteCategory.hom (Scheme.Hom.appTop m)) (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨b⟩ : ULift.{u, 0} (Fin M)))) h0`.

Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply] at h1`. Rewrite using `[h1, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]`. Establish `h2` using `pullbackCoord_translateLastCoord_inl k M a b`. Rewrite `h2` using `[pullbackCoord_def]`. Rewrite using `[h2]`.

Establish `h3` using `pullbackCoord_affineSpaceInl_inl k M 1 b`. Rewrite `h3` using `[pullbackCoord_def]`. Rewrite using `[h3]`. Rewrite using `[← lastCoordinate_eq_coord k M j, sliceAtLastCoord_appTop_lastCoordinate, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, translateLastCoord_appTop_lastCoordinate, map_add, appTop_baseFieldToGlobalSections, affineSpaceInl_comp_affineSpaceIndexedByToSpec]`. Establish `h4` using `pullbackCoord_affineSpaceInl_inr k M 1 (0 : Fin 1)`.

Rewrite `h4` using `[pullbackCoord_def]`. Rewrite using `[lastCoordinate_eq, h4, zero_add]`.
-/
private theorem sliceAtLastCoord_eq_affineSpaceInl_comp_translateLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) :
    sliceAtLastCoord k M a = affineSpaceInl k M 1 ≫ translateLastCoord k M a := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, translateLastCoord_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]
  · rintro ⟨b | j⟩
    · have h0 := sliceAtLastCoord_comp_projLeft k M a
      have h1 := congrArg
        (fun m : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶
            affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) =>
          (ConcreteCategory.hom (Scheme.Hom.appTop m))
            (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨b⟩ : ULift.{u, 0} (Fin M)))) h0
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord,
        Scheme.Hom.id_appTop, CommRingCat.id_apply] at h1
      rw [h1, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      have h2 := pullbackCoord_translateLastCoord_inl k M a b
      rw [pullbackCoord_def] at h2
      rw [h2]
      have h3 := pullbackCoord_affineSpaceInl_inl k M 1 b
      rw [pullbackCoord_def] at h3
      rw [h3]
    · rw [← lastCoordinate_eq_coord k M j, sliceAtLastCoord_appTop_lastCoordinate, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, translateLastCoord_appTop_lastCoordinate, map_add, appTop_baseFieldToGlobalSections,
        affineSpaceInl_comp_affineSpaceIndexedByToSpec]
      have h4 := pullbackCoord_affineSpaceInl_inr k M 1 (0 : Fin 1)
      rw [pullbackCoord_def] at h4
      rw [lastCoordinate_eq, h4, zero_add]

/- English proof (translation)
Establish `h1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (σ ≫ affineSpaceInl k M 1) (c + 1)` using `HasSmoothCoordCodim.comp_affineSpaceInl hsm k σ 1 hσ`. Establish `h2` using `h1.comp_iso_hom (translateLastCoordIso k M a) (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (by simp)`. Rewrite using `[sliceAtLastCoord_eq_affineSpaceInl_comp_translateLastCoord, ← Category.assoc]`. Conclude with `h2`.
-/
private theorem hasSmoothCoordCodim_comp_sliceAtLastCoord (hsm : AffineSpaceIsSmooth.{u}) (k : Type u)
    [Field k] (M c : ℕ) (a : k) {B : Scheme.{u}}
    (σ : B ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion σ]
    (hσ : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) σ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (σ ≫ sliceAtLastCoord k M a) (c + 1) := by
  have h1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (σ ≫ affineSpaceInl k M 1) (c + 1) := HasSmoothCoordCodim.comp_affineSpaceInl hsm k σ 1 hσ
  have h2 := h1.comp_iso_hom (translateLastCoordIso k M a)
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (by simp)
  rw [sliceAtLastCoord_eq_affineSpaceInl_comp_translateLastCoord, ← Category.assoc]
  exact h2

/- English proof (translation)
Rewrite using `[hasSmoothCoordCodim_iff]`. Introduce `x`. Take `⟨i, a, rfl⟩` from `sigma_ι_base_jointly_surjective A x`. Establish `hpiece` using `hasSmoothCoordCodim_comp_sliceAtLastCoord hsm k M c (e i) (ρ i) (h i)`. Rewrite `hpiece` using `[hasSmoothCoordCodim_iff]`.

Take `⟨W, hW, q, hqS, hqstruct, hkerW⟩` from `hpiece a`. Establish `: Smooth q` using `hqS`. Use `⟨W ⊓ sliceSeparatingOpen k M e i, ?_, (affineSpaceTimesLine k M).homOfLE (inf_le_left) ≫ q, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Use `show (coproductSliceMap k M e A ρ).base ((Sigma.ι A i).base a) ∈ W ⊓ sliceSeparatingOpen k M e i`. Rewrite using `[coproductSliceMap_base_sigma_ι]`.

Conclude with `⟨hW, mem_sliceSeparatingOpen k M e he A ρ i a⟩`. Rewrite using `[Category.assoc, hqstruct, ← Category.assoc, Scheme.homOfLE_ι]`. Establish `hcrux` using `comap_ker_coproductSliceMap_eq_of_le_sliceSeparatingOpen k M e A ρ i (W ⊓ sliceSeparatingOpen k M e i) inf_le_right`. Rewrite using `[Scheme.IdealSheafData.comap_comp, ← hkerW, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]`. Conclude with `hcrux`.
-/
theorem hasSmoothCoordCodim_coproductSliceMap (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    (M c : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Function.Injective e)
    (A : ι → Scheme.{u}) [∀ i, IsAffine (A i)]
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [∀ i, IsClosedImmersion (ρ i)]
    (h : ∀ i, HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (ρ i) c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (coproductSliceMap k M e A ρ) (c + 1) := by
  rw [hasSmoothCoordCodim_iff]
  intro x
  obtain ⟨i, a, rfl⟩ := sigma_ι_base_jointly_surjective A x
  have hpiece := hasSmoothCoordCodim_comp_sliceAtLastCoord hsm k M c (e i) (ρ i) (h i)
  rw [hasSmoothCoordCodim_iff] at hpiece
  obtain ⟨W, hW, q, hqS, hqstruct, hkerW⟩ := hpiece a
  have : Smooth q := hqS
  refine ⟨W ⊓ sliceSeparatingOpen k M e i, ?_,
    (affineSpaceTimesLine k M).homOfLE (inf_le_left) ≫ q, inferInstance, ?_, ?_⟩
  · show (coproductSliceMap k M e A ρ).base ((Sigma.ι A i).base a) ∈ W ⊓ sliceSeparatingOpen k M e i
    rw [coproductSliceMap_base_sigma_ι]
    exact ⟨hW, mem_sliceSeparatingOpen k M e he A ρ i a⟩
  · rw [Category.assoc, hqstruct, ← Category.assoc, Scheme.homOfLE_ι]
  · have hcrux := comap_ker_coproductSliceMap_eq_of_le_sliceSeparatingOpen k M e A ρ i (W ⊓ sliceSeparatingOpen k M e i)
      inf_le_right
    rw [Scheme.IdealSheafData.comap_comp, ← hkerW, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι,
      ← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
    exact hcrux

def componentSliceOpen (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → k) (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    (i : ι) : (∐ A).Opens :=
  (Opens.map (coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i)

/- English proof (translation)
Rewrite using `[sigma_ι_coproductSliceMap]`. Conclude with `comp_sliceAtLastCoord_appTop_sliceSeparatingFunction k M e A ρ i j`.
-/
private theorem sigma_ι_comp_coproductSliceMap_appTop_sliceSeparatingFunction (k : Type u) [Field k] (M : ℕ) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i j : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A j ≫ coproductSliceMap k M e A ρ)))
        (sliceSeparatingFunction k M e i) =
      baseFieldToGlobalSections k (ρ j ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
        (∏ l ∈ Finset.univ.erase i, (e j - e l)) := by
  rw [sigma_ι_coproductSliceMap]
  exact comp_sliceAtLastCoord_appTop_sliceSeparatingFunction k M e A ρ i j

/- English proof (translation)
Establish `hpre : (Opens.map (Sigma.ι A i ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) = (A i).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A i ≫ coproductSliceMap k M e A ρ))) (sliceSeparatingFunction k M e i))` using `Scheme.preimage_basicOpen _ _`. Rewrite using `[hpre, sigma_ι_comp_coproductSliceMap_appTop_sliceSeparatingFunction k M e A ρ i i]`. Establish `hne : (∏ l ∈ Finset.univ.erase i, (e i - e l)) ≠ 0`. Use `Finset.prod_ne_zero_iff.mpr fun l hl => ?_` and prove the remaining obligations. Conclude with `sub_ne_zero_of_ne fun hcon => (Finset.mem_erase.mp hl).1 (he hcon).symm`.

Apply `Scheme.basicOpen_of_isUnit` to reduce the goal to its premises. Conclude with `IsUnit.map (baseFieldToGlobalSections k (ρ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))) (isUnit_iff_ne_zero.mpr hne)`.
-/
private theorem preimage_sliceSeparatingOpen_self (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    (Opens.map (Sigma.ι A i ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) = ⊤ := by
  have hpre : (Opens.map (Sigma.ι A i ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) =
      (A i).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop
        (Sigma.ι A i ≫ coproductSliceMap k M e A ρ))) (sliceSeparatingFunction k M e i)) :=
    Scheme.preimage_basicOpen _ _
  rw [hpre, sigma_ι_comp_coproductSliceMap_appTop_sliceSeparatingFunction k M e A ρ i i]
  have hne : (∏ l ∈ Finset.univ.erase i, (e i - e l)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun l hl => ?_
    exact sub_ne_zero_of_ne fun hcon => (Finset.mem_erase.mp hl).1 (he hcon).symm
  apply Scheme.basicOpen_of_isUnit
  exact IsUnit.map (baseFieldToGlobalSections k (ρ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))))
    (isUnit_iff_ne_zero.mpr hne)

/- English proof (translation)
Establish `hpre : (Opens.map (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) = (A j).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A j ≫ coproductSliceMap k M e A ρ))) (sliceSeparatingFunction k M e i))` using `Scheme.preimage_basicOpen _ _`. Establish `hzero : (∏ l ∈ Finset.univ.erase i, (e j - e l)) = 0` using `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩) (sub_self (e j))`. Rewrite using `[hpre, sigma_ι_comp_coproductSliceMap_appTop_sliceSeparatingFunction k M e A ρ i j, hzero, map_zero]`. Simplify using the standard rewrite rules.
-/
private theorem preimage_sliceSeparatingOpen_of_ne (k : Type u) [Field k] (M : ℕ) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i j : ι) (hij : j ≠ i) :
    (Opens.map (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) = ⊥ := by
  have hpre : (Opens.map (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) =
      (A j).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop
        (Sigma.ι A j ≫ coproductSliceMap k M e A ρ))) (sliceSeparatingFunction k M e i)) :=
    Scheme.preimage_basicOpen _ _
  have hzero : (∏ l ∈ Finset.univ.erase i, (e j - e l)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩) (sub_self (e j))
  rw [hpre, sigma_ι_comp_coproductSliceMap_appTop_sliceSeparatingFunction k M e A ρ i j, hzero, map_zero]
  simp

/- English proof (translation)
Rewrite using `[Scheme.Opens.range_ι]`. Use `Set.Subset.antisymm ?_ ?_` and prove the remaining obligations. Introduce and unpack `x ⟨y, rfl⟩`. Establish `hy : y ∈ (Opens.map (Sigma.ι A i ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i)`. Rewrite using `[preimage_sliceSeparatingOpen_self k M e he A ρ i]`.

Simplify using the standard rewrite rules. Conclude with `hy`. Introduce `x hx`. Take `⟨j, y, rfl⟩` from `sigma_ι_base_jointly_surjective A x`. Distinguish the cases in `hij : j = i`.

Substitute `hij` using the available equality. Conclude with `Set.mem_range_self y`. It suffices to derive a contradiction. Establish `hy : y ∈ (Opens.map (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i)` using `hx`. Rewrite `hy` using `[preimage_sliceSeparatingOpen_of_ne k M e A ρ i j hij]`.

Establish `hy' : y ∈ ((⊥ : (A j).Opens) : Set ↥(A j))` using `hy`. Rewrite `hy'` using `[TopologicalSpace.Opens.coe_bot]`. Conclude with `(Set.mem_empty_iff_false y).mp hy'`.
-/
private theorem range_sigma_ι_eq_range_componentSliceOpen_ι (k : Type u) [Field k] (M : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Function.Injective e)
    (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    Set.range (Sigma.ι A i).base = Set.range (componentSliceOpen k M e A ρ i).ι.base := by
  rw [Scheme.Opens.range_ι]
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    have hy : y ∈ (Opens.map (Sigma.ι A i ≫ coproductSliceMap k M e A ρ).base).obj
        (sliceSeparatingOpen k M e i) := by
      rw [preimage_sliceSeparatingOpen_self k M e he A ρ i]
      simp
    exact hy
  · intro x hx
    obtain ⟨j, y, rfl⟩ := sigma_ι_base_jointly_surjective A x
    by_cases hij : j = i
    · subst hij
      exact Set.mem_range_self y
    · exfalso
      have hy : y ∈ (Opens.map (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base).obj
          (sliceSeparatingOpen k M e i) := hx
      rw [preimage_sliceSeparatingOpen_of_ne k M e A ρ i j hij] at hy
      have hy' : y ∈ ((⊥ : (A j).Opens) : Set ↥(A j)) := hy
      rw [TopologicalSpace.Opens.coe_bot] at hy'
      exact (Set.mem_empty_iff_false y).mp hy'

/- English proof (translation)
Establish `hrange` using `range_sigma_ι_eq_range_componentSliceOpen_ι k M e he A ρ i`. Use `⟨IsOpenImmersion.isoOfRangeEq (Sigma.ι A i) (componentSliceOpen k M e A ρ i).ι hrange, ?_⟩` and prove the remaining obligations. Apply `IsOpenImmersion.isoOfRangeEq_hom_fac` to reduce the goal to its premises.
-/
private theorem exists_iso_componentSliceOpen (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    ∃ φ : A i ≅ (↑(componentSliceOpen k M e A ρ i) : Scheme.{u}),
      φ.hom ≫ (componentSliceOpen k M e A ρ i).ι = Sigma.ι A i := by
  have hrange := range_sigma_ι_eq_range_componentSliceOpen_ι k M e he A ρ i
  refine ⟨IsOpenImmersion.isoOfRangeEq (Sigma.ι A i) (componentSliceOpen k M e A ρ i).ι hrange, ?_⟩
  apply IsOpenImmersion.isoOfRangeEq_hom_fac

def componentIsoSliceOpen (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    A i ≅ (↑(componentSliceOpen k M e A ρ i) : Scheme.{u}) :=
  (exists_iso_componentSliceOpen k M e he A ρ i).choose

@[simp]
/- English proof (translation)
The claim follows from `(exists_iso_componentSliceOpen k M e he A ρ i).choose_spec @[simp]`.
-/
theorem componentIsoSliceOpen_hom_comp_ι (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    (componentIsoSliceOpen k M e he A ρ i).hom ≫ (componentSliceOpen k M e A ρ i).ι = Sigma.ι A i :=
  (exists_iso_componentSliceOpen k M e he A ρ i).choose_spec

@[simp]
/- English proof (translation)
Rewrite using `[← Category.assoc, componentIsoSliceOpen_hom_comp_ι]`.
-/
theorem componentIsoSliceOpen_hom_comp_ι_assoc (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) {Z : Scheme.{u}}
    (g : (∐ A) ⟶ Z) :
    (componentIsoSliceOpen k M e he A ρ i).hom ≫ (componentSliceOpen k M e A ρ i).ι ≫ g =
      Sigma.ι A i ≫ g := by
  rw [← Category.assoc, componentIsoSliceOpen_hom_comp_ι]

abbrev coproductSliceMapReindexed (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) :
    (∐ A) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (M + 1))) :=
  coproductSliceMap k M e A ρ ≫
    (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M 1) (Spec (CommRingCat.of k))).hom

/- English proof (translation)
Rewrite using `[Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]`. Conclude with `coproductSliceMap_comp_affineSpaceIndexedByToSpec k M e A ρ q hq`.
-/
theorem coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k)
    (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    (q : (∐ A) ⟶ Spec (CommRingCat.of k))
    (hq : ∀ i, Sigma.ι A i ≫ q = ρ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) :
    coproductSliceMapReindexed k M e A ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))) = q := by
  rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
  exact coproductSliceMap_comp_affineSpaceIndexedByToSpec k M e A ρ q hq

/- English proof (translation)
Establish `: IsClosedImmersion (coproductSliceMap k M e A ρ)` using `isClosedImmersion_coproductSliceMap k M e he A ρ`. Conclude with `(hasSmoothCoordCodim_coproductSliceMap hsm k M c e he A ρ h).comp_iso_hom (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M 1) (Spec (CommRingCat.of k))) (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1)))) (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M 1))`.
-/
theorem hasSmoothCoordCodim_coproductSliceMapReindexed (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    (M c : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Function.Injective e)
    (A : ι → Scheme.{u}) [∀ i, IsAffine (A i)]
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [∀ i, IsClosedImmersion (ρ i)]
    (h : ∀ i, HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (ρ i) c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))))
      (coproductSliceMapReindexed k M e A ρ) (c + 1) := by
  have : IsClosedImmersion (coproductSliceMap k M e A ρ) := isClosedImmersion_coproductSliceMap k M e he A ρ
  exact (hasSmoothCoordCodim_coproductSliceMap hsm k M c e he A ρ h).comp_iso_hom
    (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M 1) (Spec (CommRingCat.of k)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))))
    (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M 1))

end FunctorialResolution.EmbeddedResolution

end
