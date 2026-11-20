import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks

open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IECobPf

/- English proof (translation)
The claim follows from `(RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange`.
-/
theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

/- English proof (translation)
Introduce `A B C D f g u v sq hf`. Use `et_cobase` as an intermediate fact. Establish `hI : IE.IsStableUnderCobaseChange`. Unfold `IE`. Use `infer_instance`.

Conclude with `hI.of_isPushout sq.flip hf`.
-/
theorem IECob_of : LateralTheory.E.ULAStalkPf.IECob := by
  intro A B C D f g u v sq hf
  have := et_cobase
  have hI : IE.IsStableUnderCobaseChange := by
    unfold IE; infer_instance
  exact hI.of_isPushout sq.flip hf

end LateralTheory.E.IECobPf
