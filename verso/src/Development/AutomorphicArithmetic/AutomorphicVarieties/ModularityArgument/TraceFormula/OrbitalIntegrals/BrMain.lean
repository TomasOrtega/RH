import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwCentImg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotAlong
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.InclClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.GeoOfMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.UnitSB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.UnitMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.GeoTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.AlongIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceUnit

namespace UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
The claim follows from `twCentImg centComm_of`.
-/
theorem twCentImg_holds : TwCentImg := twCentImg centComm_of

/- English proof (translation)
The claim follows from `quotAlong haarComm_of quotIndep_of`.
-/
theorem quotAlong_holds : QuotAlong := quotAlong haarComm_of quotIndep_of

/- English proof (translation)
The claim follows from `inclClosed extCont_of`.
-/
theorem inclClosed_holds : InclClosed := inclClosed extCont_of

/- English proof (translation)
The claim follows from `geoOfMatch gLTop_of extCont_of centComm_of twCentImg_holds quotAlong_holds inclClosed_holds`.
-/
theorem geoOfMatch_holds : GeoOfMatch := geoOfMatch gLTop_of extCont_of centComm_of twCentImg_holds quotAlong_holds inclClosed_holds

/- English proof (translation)
The claim follows from `quotReal`.
-/
theorem quotReal_holds : QuotReal := quotReal

/- English proof (translation)
The claim follows from `unitSB`.
-/
theorem unitSB_holds : UnitSB := unitSB

/- English proof (translation)
The claim follows from `unitMatch gLTop_of extCont_of centComm_of twCent_of haarComm_of quotReal_holds unitSB_holds`.
-/
theorem unitMatch_holds : UnitMatch := unitMatch gLTop_of extCont_of centComm_of twCent_of haarComm_of quotReal_holds unitSB_holds

/- English proof (translation)
The claim follows from `geoTransport`.
-/
theorem geoTransport_holds : GeoTransport := geoTransport

/- English proof (translation)
The claim follows from `alongIndep`.
-/
theorem alongIndep_holds : AlongIndep := alongIndep

/- English proof (translation)
The claim follows from `placeData`.
-/
theorem placeData_holds : PlaceData := placeData

/- English proof (translation)
The claim follows from `placeOfLocal gLTop_of extCont_of centComm_of haarComm_of twCentImg_holds geoOfMatch_holds geoTransport_holds alongIndep_holds`.
-/
theorem placeOfLocal_holds : PlaceOfLocal := placeOfLocal gLTop_of extCont_of centComm_of haarComm_of twCentImg_holds geoOfMatch_holds geoTransport_holds alongIndep_holds

/- English proof (translation)
The claim follows from `placeUniq`.
-/
theorem placeUniq_holds : PlaceUniq := placeUniq

/- English proof (translation)
The claim follows from `placeInt`.
-/
theorem placeInt_holds : PlaceInt := placeInt

/- English proof (translation)
The claim follows from `placeUnit unitMatch_holds unitSB_holds placeData_holds placeOfLocal_holds placeInt_holds`.
-/
theorem placeUnit_holds : PlaceUnit := placeUnit unitMatch_holds unitSB_holds placeData_holds placeOfLocal_holds placeInt_holds

end UpperTheory.V.Z.Tf.Orb
