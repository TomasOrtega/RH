import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelSum
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeInto
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeBij
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeY
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelDecomp
import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
import Formalism.MahlerMeasure.LevelConst

namespace Formalism.GM.Top
open Formalism.GM
/- English proof (translation)
The claim follows from `levelAct_of alternatingChooseSum`.
-/
theorem levelAct : LevelAct := levelAct_of alternatingChooseSum
end Formalism.GM.Top
