import Formalism.ThetaLiftIndependence.ThetaOrbitSums.OrbitSum
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ChainScalar
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.GaussOp
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.EigenSwap
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.FFPlancherel
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.DetSwap

namespace Formalism.ThetaLiftIndependence

/- English proof (translation)
The claim follows from `gaussOp_eq`.
-/
theorem final_gaussOp : GaussOp := gaussOp_eq

end Formalism.ThetaLiftIndependence
