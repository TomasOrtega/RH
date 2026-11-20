import Development.WeilBound.ThetaLifts.SphericalLattices.OrdDetUniformizerImageEq
import Development.WeilBound.ThetaLifts.SphericalLattices.MemRangeOfEntries
import Development.WeilBound.ThetaLifts.SphericalLattices.IntMFromBlocks
import Development.WeilBound.ThetaLifts.SphericalLattices.OneAddNe

namespace PositivityTheory.Sph.M2

/- English proof (translation)
The claim follows from `locMod_of locComm zCount gen`.
-/
theorem locMod : LocModSt := locMod_of locComm zCount gen

end PositivityTheory.Sph.M2
