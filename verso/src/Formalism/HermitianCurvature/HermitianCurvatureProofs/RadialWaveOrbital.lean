import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem radial_wave_orbital : RDWaveJ := by
  intro k r Wp Wq _ _ _ _ _ _ D s H _ g _
  unfold wvG
  exact PBFV.JF_mul_inv D _ (fun p hp x => by rw [BigCellZetaMinors.dmin_sgs D hp]) H g

end Formalism.FourierDecayAlt.P.CutSE
