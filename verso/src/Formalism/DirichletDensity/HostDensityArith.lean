import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr
import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
import Formalism.DirichletDensity.DirichletDensityProofs.LogToDir
import Formalism.DirichletDensity.DirichletDensityProofs.HostDensityArith
import Formalism.DirichletDensity.DirichletDensityProofs.HostDensity

namespace Formalism.HF.Final

/- English proof (translation)
The claim follows from `Formalism.HF.quadDiscr`.
-/
theorem quadDiscr : Formalism.HF.QuadDiscr := Formalism.HF.quadDiscr
/- English proof (translation)
The claim follows from `Formalism.HF.mqDiscr_of quadDiscr`.
-/
theorem mqDiscr : Formalism.HF.MQDiscr := Formalism.HF.mqDiscr_of quadDiscr
/- English proof (translation)
The claim follows from `Formalism.HF.hostDiscr_of mqDiscr`.
-/
theorem hostDiscr : Formalism.HF.HostDiscr := Formalism.HF.hostDiscr_of mqDiscr
/- English proof (translation)
The claim follows from `Formalism.HF.apLogDensity`.
-/
theorem apLogDensity : Formalism.HF.APLogDensity := Formalism.HF.apLogDensity
/- English proof (translation)
The claim follows from `Formalism.HF.logToDir`.
-/
theorem logToDir : Formalism.HF.LogToDir := Formalism.HF.logToDir
/- English proof (translation)
The claim follows from `Formalism.HF.hostDensityArith_of apLogDensity logToDir`.
-/
theorem hostDensityArith : Formalism.HF.HostDensityArith := Formalism.HF.hostDensityArith_of apLogDensity logToDir
/- English proof (translation)
The claim follows from `Formalism.HF.hostDensity_of hostDensityArith`.
-/
theorem hostDensity : Formalism.HF.HostDensity := Formalism.HF.hostDensity_of hostDensityArith

end Formalism.HF.Final
