import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.PickNeg
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.MorphZeroOfSec

namespace CrystallineSemistableComparison

/- English proof (translation)
Introduce `hF` and use `bock_tw (TwSeq.twSeq hF.et.gen) hF`.
-/
theorem bock : BocksteinInputFromFormal := fun hF => bock_tw (TwSeq.twSeq hF.et.gen) hF

end CrystallineSemistableComparison
