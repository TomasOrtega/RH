import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure SmoothCenterBlowup {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : Type (u + 1) where
  center : X.IdealSheafData
  center_smooth : AlgebraicGeometry.Smooth (center.subschemeι ≫ p)
  center_snc : HasStrictNormalCrossingsWith p center E
  ideal_vanishes : VanishesAlong I center
  obj : Scheme.{u}
  map : obj ⟶ X
  isBlowup : Blowup.IsBlowupAlongIdealSheaf map center
  idealUp : obj.IdealSheafData
  transform_rule : Blowup.exceptionalIdeal map center * idealUp = I.comap map

namespace SmoothCenterBlowup

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

def structureMorphism (s : SmoothCenterBlowup p I E) : s.obj ⟶ Spec (CommRingCat.of k) := s.map ≫ p

/- English proof (authored)
The structure morphism of the blown-up scheme is defined by following its blowup map with the original structure morphism.
-/
theorem structureMorphism_eq (s : SmoothCenterBlowup p I E) : s.structureMorphism = s.map ≫ p := rfl

def exceptionalIdeal (s : SmoothCenterBlowup p I E) : s.obj.IdealSheafData :=
  Blowup.exceptionalIdeal s.map s.center

/- English proof (authored)
The exceptional ideal of a blowup is the pullback of the center ideal along the blowup map. This is the exceptional ideal of the given step.
-/
theorem exceptionalIdeal_eq (s : SmoothCenterBlowup p I E) : s.exceptionalIdeal = s.center.comap s.map := rfl

def boundary (s : SmoothCenterBlowup p I E) : List s.obj.IdealSheafData :=
  E.map (Blowup.strictTransform s.map s.center) ++ [s.exceptionalIdeal]

/- English proof (authored)
The new boundary is defined by taking the strict transform of each entry of the old list in order and then appending the exceptional ideal.
-/
theorem boundary_eq (s : SmoothCenterBlowup p I E) :
    s.boundary = E.map (Blowup.strictTransform s.map s.center) ++ [s.exceptionalIdeal] := rfl

end SmoothCenterBlowup

structure IdealBlowupSequence {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, (toSequenceOfBlowups.schemeAt i).IdealSheafData
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap (toSequenceOfBlowups.projectionToBase 0)
  boundary_zero : boundary 0 = E.map (fun D => D.comap (toSequenceOfBlowups.projectionToBase 0))
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    AlgebraicGeometry.Smooth
      ((toSequenceOfBlowups.center i).subschemeι ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  ideal_vanishes : ∀ i, i < toSequenceOfBlowups.length →
    VanishesAlong (ideal i) (toSequenceOfBlowups.center i)
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)) ++
        [Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)]

namespace IdealBlowupSequence

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

def structureMorphism (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.toSequenceOfBlowups.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p

/- English proof (authored)
The structural map at this stage is the projection to the original scheme followed by that scheme's morphism to the field spectrum.
-/
theorem structureMorphism_def (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.structureMorphism i = s.toSequenceOfBlowups.projectionToBase i ≫ p := rfl

/- English proof (authored)
The sequence includes smoothness of each actual center over the field. The composite in that condition is exactly the center inclusion followed by this stage's structure morphism.
-/
theorem smooth_center_subschemeι (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.Smooth ((s.toSequenceOfBlowups.center i).subschemeι ≫ s.structureMorphism i) :=
  s.center_smooth i h

/- English proof (authored)
The sequence's center condition gives strict normal crossings with the current boundary at every valid index. Apply it at the specified stage.
-/
theorem hasStrictNormalCrossingsWith_center (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    HasStrictNormalCrossingsWith (s.structureMorphism i) (s.toSequenceOfBlowups.center i) (s.boundary i) :=
  s.center_snc i h

def exceptionalIdeal (s : IdealBlowupSequence p I E) (i : ℕ) : (s.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData :=
  Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)

/- English proof (authored)
At this stage the exceptional ideal is the center ideal pulled back by the transition map of its blowup.
-/
theorem exceptionalIdeal_eq (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.exceptionalIdeal i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := rfl

/- English proof (authored)
The transition rule in the sequence takes the strict transforms of the entries of the current boundary and appends the exceptional ideal of the step. Apply that rule at the given valid index.
-/
theorem boundary_succ_eq_map_strictTransform_append (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    s.boundary (i + 1) =
      (s.boundary i).map
          (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)) ++
        [s.exceptionalIdeal i] :=
  s.boundary_succ i h

def lastIdeal (s : IdealBlowupSequence p I E) :
    (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.ideal s.toSequenceOfBlowups.length

/- English proof (authored)
The last ideal is defined by evaluating the stage ideals at the length of the sequence.
-/
theorem lastIdeal_eq (s : IdealBlowupSequence p I E) :
    s.lastIdeal = s.ideal s.toSequenceOfBlowups.length := rfl

def lastBoundary (s : IdealBlowupSequence p I E) :
    List (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.boundary s.toSequenceOfBlowups.length

/- English proof (authored)
The last boundary is the boundary at the final index, which is the length of the sequence.
-/
theorem lastBoundary_eq (s : IdealBlowupSequence p I E) :
    s.lastBoundary = s.boundary s.toSequenceOfBlowups.length := rfl

end IdealBlowupSequence

end FunctorialResolution.EmbeddedResolution
