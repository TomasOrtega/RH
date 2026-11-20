import Mathlib
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowups

variable {X : Scheme.{u}}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem transitionMap_def (s : SequenceOfBlowups X) {i i' : ℕ} (h : i ≤ i') :
    s.transitionMap h = s.tower.map (homOfLE h).op := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transitionMap_trans (s : SequenceOfBlowups X) {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    s.transitionMap hjl ≫ s.transitionMap hij = s.transitionMap (hij.trans hjl) :=
  (s.tower.map_comp (homOfLE hjl).op (homOfLE hij).op).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem transitionMap_self (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i) : s.transitionMap h = 𝟙 (s.schemeAt i) := by
  rw [transitionMap_def, show (homOfLE h).op = 𝟙 (op i) from rfl, s.tower.map_id]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blowupMorphism_eq_transitionMap (s : SequenceOfBlowups X) (i : ℕ) :
    s.transitionMapSucc i = s.transitionMap (Nat.le_succ i) := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isBlowupAlongIdealSheaf_blowupMorphism (s : SequenceOfBlowups X) (i : ℕ) (h : i < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowup i h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem projectionToBase_def (s : SequenceOfBlowups X) (i : ℕ) :
    s.projectionToBase i = s.transitionMap (Nat.zero_le i) ≫ s.isoZero.hom := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem projectionToBase_zero (s : SequenceOfBlowups X) : s.projectionToBase 0 = s.isoZero.hom := by
  rw [projectionToBase_def, s.transitionMap_self, Category.id_comp]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem projectionToBase_succ (s : SequenceOfBlowups X) (i : ℕ) :
    s.projectionToBase (i + 1) = s.transitionMapSucc i ≫ s.projectionToBase i := by
  rw [blowupMorphism_eq_transitionMap]
  exact (s.transitionMap_comp_projectionToBase (Nat.le_succ i)).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lastStructMap_eq_projectionToBase (s : SequenceOfBlowups X) : s.lastStructMap = s.projectionToBase s.length := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pullbackTransitionMap_fst (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.fst φ (s.projectionToBase i) = pullback.fst φ (s.projectionToBase i') :=
  Eq.trans (pullback.lift_fst _ _ _) (Category.comp_id _)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pullbackTransitionMap_snd (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.snd φ (s.projectionToBase i)
      = pullback.snd φ (s.projectionToBase i') ≫ s.transitionMap h :=
  pullback.lift_snd _ _ _

end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
