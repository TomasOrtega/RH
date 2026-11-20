import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.MirrorDecompOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StabPairs
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EichlerTau
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LowUniSplit

/- English proof (translation)
The claim follows from `PI.MirrorSection₂.mirrorDecomp_of stabPairs eichlerTau lowUniSplit`.
-/
theorem mirrorDecomp : Formalism.FourierDecayAlt.C2.MirrorDecomp :=
  PI.MirrorSection₂.mirrorDecomp_of stabPairs eichlerTau lowUniSplit
