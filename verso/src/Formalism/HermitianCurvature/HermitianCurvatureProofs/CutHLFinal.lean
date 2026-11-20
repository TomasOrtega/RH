import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadLetterOfMinusPos
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLMinusPosOfParts

namespace Formalism.FourierDecayAlt.P.CutHL

/- English proof (translation)
The claim follows from `headLetter_of_minusPos Formalism.FourierDecayAlt.P.minus_positive_of_parts`.
-/
theorem head_letter_of_minus_positive : LevelPointCoordinates.HeadLetter :=
  headLetter_of_minusPos Formalism.FourierDecayAlt.P.minus_positive_of_parts

end Formalism.FourierDecayAlt.P.CutHL

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.CutHL.head_letter_of_minus_positive`.
-/
theorem Formalism.FourierDecayAlt.P.head_letter_identity : Formalism.FourierDecayAlt.P.LevelPointCoordinates.HeadLetter := Formalism.FourierDecayAlt.P.CutHL.head_letter_of_minus_positive
