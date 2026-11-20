import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem Dominates.equiv (A : Type*) {K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    [Algebra A K] (V : Subring K) :
    GroundTheory.Heights₂.Heights.Model.Dominates A V ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.Dominates A V :=
  Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun A K _ _ _ _ _ _ _ hA => ?_, fun Z _ _ z hz => ?_⟩` and prove the remaining obligations. Take `⟨V, hV, hd⟩` from `h1 A hA K`. Conclude with `⟨V, hV, (Dominates.equiv A V).1 hd⟩`.

Take `⟨V, hV, hd⟩` from `h2 Z z hz`. Conclude with `⟨V, hV, (Dominates.equiv _ V).1 hd⟩`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun A _ _ _ _ hA K _ _ _ => ?_, fun Z _ _ z hz => ?_⟩` and prove the remaining obligations. Take `⟨V, hV, hd⟩` from `h1 A K hA`.

Conclude with `⟨V, hV, (Dominates.equiv A V).2 hd⟩`. Take `⟨V, hV, hd⟩` from `h2 Z z hz`. Conclude with `⟨V, hV, (Dominates.equiv _ V).2 hd⟩`.
-/
theorem DominatingDVR.equiv :
    (GroundTheory.Heights₂.Heights.Model.DominatingDVR.Statement ∧
        GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.Statement) ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.DominatingDVR.Statement := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun A K _ _ _ _ _ _ _ hA => ?_, fun Z _ _ z hz => ?_⟩
    · obtain ⟨V, hV, hd⟩ := h1 A hA K
      exact ⟨V, hV, (Dominates.equiv A V).1 hd⟩
    · obtain ⟨V, hV, hd⟩ := h2 Z z hz
      exact ⟨V, hV, (Dominates.equiv _ V).1 hd⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun A _ _ _ _ hA K _ _ _ => ?_, fun Z _ _ z hz => ?_⟩
    · obtain ⟨V, hV, hd⟩ := h1 A K hA
      exact ⟨V, hV, (Dominates.equiv A V).2 hd⟩
    · obtain ⟨V, hV, hd⟩ := h2 Z z hz
      exact ⟨V, hV, (Dominates.equiv _ V).2 hd⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
