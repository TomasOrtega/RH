import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormFsvSubOnePow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDifferenceForm

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def DecayUnifOfParts : Prop := KB.RadHead → KB.HeadTop → WaveDiffForm → DecayUnif

def DecayUnifOfHeads : Prop := KB.RadHead → KB.HeadTop → DecayUnif

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem decayUnifOfHeads : DecayUnifOfHeads := fun hRH hHT =>
  decayUnif_of hRH hHT Formalism.FourierDecayAlt.P.wave_difference_form

end Formalism.FourierDecayAlt.P.PBO

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Formalism.FourierDecayAlt.P.uniform_decay_of_heads : Formalism.FourierDecayAlt.P.PBO.DecayUnifOfHeads := Formalism.FourierDecayAlt.P.PBO.decayUnifOfHeads
