import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

open Classical in
noncomputable def residualByPow {Y : Scheme.{u}} (A F : Y.IdealSheafData) (m : ℕ) : Y.IdealSheafData :=
  if h : ∃ B : Y.IdealSheafData, F ^ m * B = A then h.choose else ⊤

/- English proof (authored)
The hypothesis supplies a residual ideal whose product with the given power is the original ideal. The residual construction chooses one such ideal, so it satisfies that identity.
-/
theorem pow_mul_residualByPow {Y : Scheme.{u}} (A F : Y.IdealSheafData) (m : ℕ)
    (h : ∃ B : Y.IdealSheafData, F ^ m * B = A) : F ^ m * residualByPow A F m = A := by
  have hx : residualByPow A F m = h.choose := dif_pos h
  rw [hx]
  exact h.choose_spec

/- English proof (authored)
Pullback along the identity fixes every ideal. Applying it in order to every entry therefore returns the original list.
-/
private theorem map_comap_id_list_idealSheafData {X : Scheme.{u}} (E : List X.IdealSheafData) :
    E.map (fun D => D.comap (𝟙 X)) = E := by
  induction E with
  | nil => rfl
  | cons a t ih => simp [Scheme.IdealSheafData.comap_id]

@[simp]
/- English proof (authored)
The exceptional ideal is the center ideal pulled back along the morphism. With the identity morphism this pullback equals the center ideal.
-/
theorem exceptionalIdeal_id {X : Scheme.{u}} (Z : X.IdealSheafData) :
    Blowup.exceptionalIdeal (𝟙 X) Z = Z := by
  rw [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]

private def singleBlowupScheme {X : Scheme.{u}} (Z : X.IdealSheafData) : ℕ → Scheme.{u}
  | 0 => X
  | (_ + 1) => Blowup.blowup Z

private def singleBlowupMap {X : Scheme.{u}} (Z : X.IdealSheafData) :
    ∀ i : ℕ, singleBlowupScheme Z (i + 1) ⟶ singleBlowupScheme Z i
  | 0 => Blowup.blowup.proj Z
  | (_ + 1) => 𝟙 (Blowup.blowup Z)

private def singleBlowupCenter {X : Scheme.{u}} (Z : X.IdealSheafData) :
    ∀ i : ℕ, (singleBlowupScheme Z i).IdealSheafData
  | 0 => Z
  | (_ + 1) => ⊤

private def singleBlowupProj {X : Scheme.{u}} (Z : X.IdealSheafData) : ∀ i : ℕ, singleBlowupScheme Z i ⟶ X
  | 0 => 𝟙 X
  | (_ + 1) => Blowup.blowup.proj Z

private def singleBlowupResidualIdeal {X : Scheme.{u}} (I Z : X.IdealSheafData) (m : ℕ) :
    ∀ i : ℕ, (singleBlowupScheme Z i).IdealSheafData
  | 0 => I.comap (𝟙 X)
  | (_ + 1) => residualByPow (I.comap (Blowup.blowup.proj Z)) (Z.comap (Blowup.blowup.proj Z)) m

private def singleBlowupBoundary {X : Scheme.{u}} (Z : X.IdealSheafData) (E : List X.IdealSheafData) :
    ∀ i : ℕ, List (singleBlowupScheme Z i).IdealSheafData
  | 0 => E.map (fun D => D.comap (𝟙 X))
  | (_ + 1) =>
      E.map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++ [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z]

/- English proof (authored)
The only index below one is zero. At that index the map is the canonical blowup projection of the given ideal, which has the required blowup property.
-/
private theorem isBlowupAlongIdealSheaf_singleBlowupMap {X : Scheme.{u}} (Z : X.IdealSheafData) (i : ℕ) (hi : i < 1) :
    Blowup.IsBlowupAlongIdealSheaf (singleBlowupMap Z i) (singleBlowupCenter Z i) := by
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show Blowup.IsBlowupAlongIdealSheaf (Blowup.blowup.proj Z) Z
  exact Blowup.blowup.isBlowupAlongIdealSheaf_proj Z

private def singleBlowupSequenceData {X : Scheme.{u}} (Z : X.IdealSheafData) : BlowupSequenceData X where
  length := 1
  obj := singleBlowupScheme Z
  map := singleBlowupMap Z
  isoZero := Iso.refl X
  center := singleBlowupCenter Z
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_singleBlowupMap Z i hi

/- English proof (authored)
At index zero the transition is the blowup projection and the preceding projection is the identity on the original scheme. At any later index the transition is the identity on the blowup and the preceding projection is the blowup projection. Both composites give the stated successor projection.
-/
private theorem singleBlowupProj_succ {X : Scheme.{u}} (Z : X.IdealSheafData) (i : ℕ) :
    singleBlowupProj Z (i + 1) = singleBlowupMap Z i ≫ singleBlowupProj Z i := by
  cases i with
  | zero =>
      show Blowup.blowup.proj Z = Blowup.blowup.proj Z ≫ 𝟙 X
      exact (Category.comp_id _).symm
  | succ j =>
      show Blowup.blowup.proj Z = 𝟙 (Blowup.blowup Z) ≫ Blowup.blowup.proj Z
      exact (Category.id_comp _).symm

/- English proof (authored)
The bound on the index forces it to be zero. There the center is the given ideal and the stage ideal is the original ideal pulled back along the identity. The asserted support containment is therefore the given order condition.
-/
private theorem singleBlowupCenter_support_subset_orderAtLeastLocus {X : Scheme.{u}} (I Z : X.IdealSheafData) (m : ℕ)
    (hord : (Z.support : Set ↥X) ⊆ orderAtLeastLocus I m) :
    ∀ i : ℕ, i < 1 →
      ((singleBlowupCenter Z i).support : Set ↥(singleBlowupScheme Z i)) ⊆ orderAtLeastLocus (singleBlowupResidualIdeal I Z m i) m := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show (Z.support : Set ↥X) ⊆ orderAtLeastLocus (I.comap (𝟙 X)) m
  rw [Scheme.IdealSheafData.comap_id]
  exact hord

/- English proof (authored)
The only active center is at index zero, and its stage projection is the identity. Its composite field map is the given smooth center map.
-/
private theorem smooth_singleBlowupCenter_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} (Z : X.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)) :
    ∀ i : ℕ, i < 1 →
      AlgebraicGeometry.Smooth ((singleBlowupCenter Z i).subschemeι ≫ singleBlowupProj Z i ≫ p) := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show AlgebraicGeometry.Smooth (Z.subschemeι ≫ 𝟙 X ≫ p)
  rw [Category.id_comp]
  exact hsm

/- English proof (authored)
The only index in range is zero. The initial projection is the identity and pulling back the original boundary along it leaves the list unchanged. Thus the crossing condition is exactly the original hypothesis.
-/
private theorem hasStrictNormalCrossingsWith_singleBlowupCenter {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z E) :
    ∀ i : ℕ, i < 1 →
      HasStrictNormalCrossingsWith (singleBlowupProj Z i ≫ p) (singleBlowupCenter Z i) (singleBlowupBoundary Z E i) := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show HasStrictNormalCrossingsWith (𝟙 X ≫ p) Z (E.map (fun D => D.comap (𝟙 X)))
  rw [map_comap_id_list_idealSheafData E, Category.id_comp]
  exact hsnc

/- English proof (authored)
At the only active index, zero, the exceptional ideal is the center pulled back to the blowup, and the preceding ideal is the original ideal. The successor ideal is chosen as a residual factor. The assumed divisibility ensures that multiplying this factor by the exceptional power gives the pulled-back original ideal.
-/
private theorem exceptionalIdeal_pow_mul_singleBlowupResidualIdeal_succ {X : Scheme.{u}} (I Z : X.IdealSheafData) (m : ℕ)
    (hdiv : ∃ B : (Blowup.blowup Z).IdealSheafData,
      (Z.comap (Blowup.blowup.proj Z)) ^ m * B = I.comap (Blowup.blowup.proj Z)) :
    ∀ i : ℕ, i < 1 →
      Blowup.exceptionalIdeal (singleBlowupMap Z i) (singleBlowupCenter Z i) ^ m * singleBlowupResidualIdeal I Z m (i + 1) =
        (singleBlowupResidualIdeal I Z m i).comap (singleBlowupMap Z i) := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z ^ m *
      residualByPow (I.comap (Blowup.blowup.proj Z)) (Z.comap (Blowup.blowup.proj Z)) m =
    (I.comap (𝟙 X)).comap (Blowup.blowup.proj Z)
  rw [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact pow_mul_residualByPow _ _ _ hdiv

/- English proof (authored)
There is only one active transition. The initial boundary is the original list, since its defining pullback is along the identity. The boundary on the blowup is defined by taking its strict transforms and appending the exceptional ideal, giving the successor identity.
-/
private theorem singleBlowupBoundary_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    ∀ i : ℕ, i < 1 →
      singleBlowupBoundary Z E (i + 1) =
        (singleBlowupBoundary Z E i).map (Blowup.strictTransform (singleBlowupMap Z i) (singleBlowupCenter Z i)) ++
          [Blowup.exceptionalIdeal (singleBlowupMap Z i) (singleBlowupCenter Z i)] := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show E.map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++ [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z] =
      (E.map (fun D => D.comap (𝟙 X))).map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++
        [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z]
  rw [map_comap_id_list_idealSheafData E]

namespace MarkedBlowupSequenceData

def ofSingleBlowup {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (Z : X.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p))
    (hsnc : HasStrictNormalCrossingsWith p Z E)
    (hord : (Z.support : Set ↥X) ⊆ orderAtLeastLocus I m)
    (hdiv : ∃ B : (Blowup.blowup Z).IdealSheafData,
      (Z.comap (Blowup.blowup.proj Z)) ^ m * B = I.comap (Blowup.blowup.proj Z)) :
    MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := singleBlowupSequenceData Z
  proj := singleBlowupProj Z
  proj_zero := rfl
  proj_succ := fun i => singleBlowupProj_succ Z i
  ideal := singleBlowupResidualIdeal I Z m
  boundary := singleBlowupBoundary Z E
  ideal_zero := rfl
  boundary_zero := rfl
  center_order := singleBlowupCenter_support_subset_orderAtLeastLocus I Z m hord
  center_smooth := smooth_singleBlowupCenter_of_smooth Z hsm
  center_snc := hasStrictNormalCrossingsWith_singleBlowupCenter Z E hsnc
  ideal_succ := exceptionalIdeal_pow_mul_singleBlowupResidualIdeal_succ I Z m hdiv
  boundary_succ := singleBlowupBoundary_succ Z E

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {Z : X.IdealSheafData}
  (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)) (hsnc : HasStrictNormalCrossingsWith p Z E)
  (hord : (Z.support : Set ↥X) ⊆ orderAtLeastLocus I m)
  (hdiv : ∃ B : (Blowup.blowup Z).IdealSheafData,
    (Z.comap (Blowup.blowup.proj Z)) ^ m * B = I.comap (Blowup.blowup.proj Z))

@[simp]
/- English proof (authored)
The sequence data are defined with one active transition.
-/
theorem ofSingleBlowup_length :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.length = 1 := rfl

@[simp]
/- English proof (authored)
The scheme assignment uses the blowup scheme at every positive index.
-/
theorem ofSingleBlowup_schemeAt_succ (i : ℕ) :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.obj (i + 1) = Blowup.blowup Z := rfl

/- English proof (authored)
The scheme at index zero is defined to be the given original scheme.
-/
theorem ofSingleBlowup_schemeAt_zero :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.obj 0 = X := rfl

/- English proof (authored)
The transition at zero is defined to be the canonical map from the blowup of the given center to the original scheme.
-/
theorem ofSingleBlowup_blowupMorphism_zero :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.map 0 = Blowup.blowup.proj Z := rfl

/- English proof (authored)
The projection at the first positive stage is defined as the blowup projection.
-/
theorem ofSingleBlowup_projectionToBase_one :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).proj 1 = Blowup.blowup.proj Z := rfl

/- English proof (authored)
The center assignment uses the given ideal at the initial stage.
-/
theorem ofSingleBlowup_center_zero :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.center 0 = Z := rfl

/- English proof (authored)
The ideal at the positive stage is defined by taking a residual factor of the pulled-back original ideal with respect to the indicated power of the pulled-back center ideal.
-/
theorem ofSingleBlowup_ideal_one :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).ideal 1 =
      residualByPow (I.comap (Blowup.blowup.proj Z)) (Z.comap (Blowup.blowup.proj Z)) m := rfl

/- English proof (authored)
At the positive stage the boundary consists of the strict transforms of the original list followed by the exceptional ideal of the blowup.
-/
theorem ofSingleBlowup_boundary_one :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).boundary 1 =
      E.map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++ [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z] := rfl

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution
