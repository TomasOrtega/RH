import Development.WeilBound.ThetaLifts.SphericalLattices.RelIndexTransport
import Development.WeilBound.ThetaLifts.SphericalLattices.LocMod
import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFrameLag

namespace PositivityTheory.Sph

/- English proof (translation)
The claim follows from `M2.modSt_of M2.chart M2.locMod`.
-/
theorem modSt2 : ModSt := M2.modSt_of M2.chart M2.locMod

end PositivityTheory.Sph
