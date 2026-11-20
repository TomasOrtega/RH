import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelSetsSL2Adelic
import GroundTheory.IdeleRoots.ClassicalIdeles.ExistsPosBoundsOfIsCompact

namespace GlobalTheory.CompanionTheory.Classical

/- English proof (translation)
The claim follows from `GroundTheory.BlockD.siegelSetsSL2Adelic_holds`.
-/
theorem siegelSetsSL2Adelic_tie : Formalism.D.siegelSetsSL2Adelic :=
  GroundTheory.BlockD.siegelSetsSL2Adelic_holds

end GlobalTheory.CompanionTheory.Classical
