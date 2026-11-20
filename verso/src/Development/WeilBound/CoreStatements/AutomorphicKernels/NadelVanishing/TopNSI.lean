import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopNadel
import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopIsolated
import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopPointSep

namespace NadelVanishingSeparation.NSI

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem nadelVanishingAndNonKltDivisor : GlobalTheory.Published.NadelVanishingAndNonKltDivisor :=
  ⟨nadelVanishingPair, isolatedNonKltDivisor⟩

end NadelVanishingSeparation.NSI
