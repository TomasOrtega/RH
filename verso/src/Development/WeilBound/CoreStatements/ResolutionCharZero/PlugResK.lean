import Mathlib
import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResW
import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugPrincW

namespace PositivityTheory.ResPlug.FromRes

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement :=
  PositivityTheory.ResPlug.resK_of_weak resW princW

end PositivityTheory.ResPlug.FromRes
