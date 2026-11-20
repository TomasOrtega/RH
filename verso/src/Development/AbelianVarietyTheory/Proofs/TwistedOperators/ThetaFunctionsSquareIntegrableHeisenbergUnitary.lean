import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSquare

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thetaFunctions_squareIntegrable_heisenbergUnitary : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.ThetaSquareIntegrable D :=
  GlobalTheory.ThetaSquare.theta_square_integrable

end GlobalTheory.ThetaSquare
