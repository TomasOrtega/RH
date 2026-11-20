import Mathlib
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowups

variable {X : Scheme.{u}}

/- English proof (authored)
The tower is indexed by the opposite of the ordered set of stages. The transition from the later stage to the earlier stage is, by definition, the image under the tower functor of the opposite of the indicated order arrow.
-/
theorem transitionMap_def (s : SequenceOfBlowups X) {i i' : ℕ} (h : i ≤ i') :
    s.transitionMap h = s.tower.map (homOfLE h).op := rfl

/- English proof (authored)
The composite of the order arrows from the first stage to the intermediate stage and from there to the last stage is the order arrow for the transitive inequality. Take opposites, which reverse the order of composition, and apply functoriality of the tower.
-/
theorem transitionMap_trans (s : SequenceOfBlowups X) {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    s.transitionMap hjl ≫ s.transitionMap hij = s.transitionMap (hij.trans hjl) :=
  (s.tower.map_comp (homOfLE hjl).op (homOfLE hij).op).symm

/- English proof (authored)
The order arrow from a stage to itself is the identity, and its opposite is also the identity. The tower functor preserves identities.
-/
theorem transitionMap_self (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i) : s.transitionMap h = 𝟙 (s.schemeAt i) := by
  rw [transitionMap_def, show (homOfLE h).op = 𝟙 (op i) from rfl, s.tower.map_id]

/- English proof (authored)
A successor transition is defined using the order arrow from its stage to the next natural number in the opposite indexing category.
-/
theorem blowupMorphism_eq_transitionMap (s : SequenceOfBlowups X) (i : ℕ) :
    s.transitionMapSucc i = s.transitionMap (Nat.le_succ i) := rfl

/- English proof (authored)
For every index strictly below the length, the data of the sequence identify the successor transition as the blowup along the center ideal of that index. Apply this property at the given index.
-/
theorem isBlowupAlongIdealSheaf_blowupMorphism (s : SequenceOfBlowups X) (i : ℕ) (h : i < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowup i h

/- English proof (authored)
The projection to the base is defined by taking the transition to stage zero and then applying the chosen isomorphism from stage zero to the base.
-/
theorem projectionToBase_def (s : SequenceOfBlowups X) (i : ℕ) :
    s.projectionToBase i = s.transitionMap (Nat.zero_le i) ≫ s.isoZero.hom := rfl

/- English proof (authored)
At stage zero the transition to zero is the identity. Composing it with the chosen initial isomorphism gives that isomorphism itself.
-/
theorem projectionToBase_zero (s : SequenceOfBlowups X) : s.projectionToBase 0 = s.isoZero.hom := by
  rw [projectionToBase_def, s.transitionMap_self, Category.id_comp]

/- English proof (authored)
Factor the transition from the successor stage to stage zero through its preceding stage. Composing with the initial isomorphism gives the successor transition followed by the preceding projection to the base.
-/
theorem projectionToBase_succ (s : SequenceOfBlowups X) (i : ℕ) :
    s.projectionToBase (i + 1) = s.transitionMapSucc i ≫ s.projectionToBase i := by
  rw [blowupMorphism_eq_transitionMap]
  exact (s.transitionMap_comp_projectionToBase (Nat.le_succ i)).symm

/- English proof (authored)
The last structural map is defined as the projection to the base at the index equal to the length of the sequence.
-/
theorem lastStructMap_eq_projectionToBase (s : SequenceOfBlowups X) : s.lastStructMap = s.projectionToBase s.length := rfl

/- English proof (authored)
The pulled-back transition is the map furnished by the pullback universal property. Its first prescribed projection is the first projection from the later pullback, with an identity on the new base. Removing that identity gives the formula.
-/
theorem pullbackTransitionMap_fst (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.fst φ (s.projectionToBase i) = pullback.fst φ (s.projectionToBase i') :=
  Eq.trans (pullback.lift_fst _ _ _) (Category.comp_id _)

/- English proof (authored)
The pullback universal property prescribes the second projection of the lifted map as projection from the later pullback followed by the original transition on the tower.
-/
theorem pullbackTransitionMap_snd (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.snd φ (s.projectionToBase i)
      = pullback.snd φ (s.projectionToBase i') ≫ s.transitionMap h :=
  pullback.lift_snd _ _ _

end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
