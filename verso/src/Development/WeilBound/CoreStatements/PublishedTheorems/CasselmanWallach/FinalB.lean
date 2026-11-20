import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CwOf
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EtaleCohomologyNegativeVanishingDegreeZero

namespace PositivityTheory.CWB

open PositivityTheory.CW

/- English proof (translation)
The claim follows from `cw_of maxPr`.
-/
theorem casselmanWallach : GlobalTheory.Published.CasselmanWallach := cw_of maxPr

end PositivityTheory.CWB
