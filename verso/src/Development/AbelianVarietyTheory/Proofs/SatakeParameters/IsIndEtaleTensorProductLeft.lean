import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

open CategoryTheory

namespace GlobalTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isIndEtale_tensorProduct_left (C A M : Type) [CommRing C] [CommRing A] [CommRing M]
    [Algebra C A] [Algebra C M] (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap C A)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap M (TensorProduct C M A)) := by
  haveI : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := MorphismProperty.ind.{0}
    (RingHom.toMorphismProperty @RingHom.Etale))
    (CommRingCat.isPushout_tensorProduct C M A) h

/- English proof (translation)
A detailed English derivation is pending.
-/
example : ∀ (C A M : Type) [CommRing C] [CommRing A] [CommRing M] [Algebra C A] [Algebra C M],
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap C A) →
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap M (TensorProduct C M A)) :=
  @isIndEtale_tensorProduct_left

end GlobalTheory
