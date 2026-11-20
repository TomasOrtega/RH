import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedOfLocSub
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LocSubOf
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.FrobRecipHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsProj2
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.RestrictAtPointHolds

namespace PositivityTheory.Rg.Rs

/- English proof (translation)
The claim follows from `LsTop.locSub_of C3.Rap.restrictAtPoint_holds existsProj2 frobRecip_holds`.
-/
theorem locSub_holds2 : LocSub := LsTop.locSub_of C3.Rap.restrictAtPoint_holds existsProj2 frobRecip_holds

/- English proof (translation)
The claim follows from `ascSeed_of_locSub locSub_holds2`.
-/
theorem ascSeed_holds2 : AscSeed := ascSeed_of_locSub locSub_holds2

end PositivityTheory.Rg.Rs
