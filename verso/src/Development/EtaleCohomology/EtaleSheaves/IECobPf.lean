import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks

open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IECobPf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem IECob_of : LateralTheory.E.ULAStalkPf.IECob := by
  intro A B C D f g u v sq hf
  have := et_cobase
  have hI : IE.IsStableUnderCobaseChange := by
    unfold IE; infer_instance
  exact hI.of_isPushout sq.flip hf

end LateralTheory.E.IECobPf
