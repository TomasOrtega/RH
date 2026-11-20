import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwCent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Unimod
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.FinPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotMass
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotFubini
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ConvTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.AbsComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Untwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwOrbFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.OrbFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwOrbLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.OrbLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwOrbComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.OrbComm

namespace UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
The claim follows from `gLTop`.
-/
theorem gLTop_of : GLTop := gLTop

/- English proof (translation)
The claim follows from `extCont`.
-/
theorem extCont_of : ExtCont := extCont

/- English proof (translation)
The claim follows from `centComm`.
-/
theorem centComm_of : CentComm := centComm

/- English proof (translation)
The claim follows from `twCent extCont_of gLTop_of centComm_of`.
-/
theorem twCent_of : TwCent := twCent extCont_of gLTop_of centComm_of

/- English proof (translation)
The claim follows from `unimod gLTop_of`.
-/
theorem unimod_of : Unimod := unimod gLTop_of

/- English proof (translation)
The claim follows from `finPres`.
-/
theorem finPres_of : FinPres := finPres

/- English proof (translation)
The claim follows from `haarComm`.
-/
theorem haarComm_of : HaarComm := haarComm

/- English proof (translation)
The claim follows from `haarConj`.
-/
theorem haarConj_of : HaarConj := haarConj

/- English proof (translation)
The claim follows from `quotIndep`.
-/
theorem quotIndep_of : QuotIndep := quotIndep

/- English proof (translation)
The claim follows from `quotConj haarComm_of quotIndep_of`.
-/
theorem quotConj_of : QuotConj := quotConj haarComm_of quotIndep_of

/- English proof (translation)
The claim follows from `quotScale quotIndep_of`.
-/
theorem quotScale_of : QuotScale := quotScale quotIndep_of

/- English proof (translation)
The claim follows from `normEx`.
-/
theorem normEx_of : NormEx := normEx

/- English proof (translation)
The claim follows from `quotMass`.
-/
theorem quotMass_of : QuotMass := quotMass

/- English proof (translation)
The claim follows from `quotInt quotMass_of`.
-/
theorem quotInt_of : QuotInt := quotInt quotMass_of

/- English proof (translation)
The claim follows from `quotPos quotIndep_of quotInt_of quotMass_of`.
-/
theorem quotPos_of : QuotPos := quotPos quotIndep_of quotInt_of quotMass_of

/- English proof (translation)
The claim follows from `quotRight quotIndep_of`.
-/
theorem quotRight_of : QuotRight := quotRight quotIndep_of

/- English proof (translation)
The claim follows from `quotFubini quotMass_of`.
-/
theorem quotFubini_of : QuotFubini := quotFubini quotMass_of

/- English proof (translation)
The claim follows from `convTest`.
-/
theorem convTest_of : ConvTest := convTest

/- English proof (translation)
The claim follows from `absComm quotFubini_of quotRight_of finPres_of`.
-/
theorem absComm_of : AbsComm := absComm quotFubini_of quotRight_of finPres_of

/- English proof (translation)
The claim follows from `untwist`.
-/
theorem untwist_of : Untwist := untwist

/- English proof (translation)
The claim follows from `twOrbFin gLTop_of extCont_of twCent_of h haarComm_of normEx_of quotInt_of quotPos_of`.
-/
theorem twOrbFin_of (h : OrbProper) : TwOrbFin := twOrbFin gLTop_of extCont_of twCent_of h haarComm_of normEx_of quotInt_of quotPos_of

/- English proof (translation)
The claim follows from `orbFin (twOrbFin_of h) untwist_of`.
-/
theorem orbFin_of (h : OrbProper) : OrbFin := orbFin (twOrbFin_of h) untwist_of

/- English proof (translation)
The claim follows from `twOrbLin (twOrbFin_of h)`.
-/
theorem twOrbLin_of (h : OrbProper) : TwOrbLin := twOrbLin (twOrbFin_of h)

/- English proof (translation)
The claim follows from `orbLin (twOrbLin_of h) untwist_of`.
-/
theorem orbLin_of (h : OrbProper) : OrbLin := orbLin (twOrbLin_of h) untwist_of

/- English proof (translation)
The claim follows from `twOrbComm gLTop_of extCont_of twCent_of h haarComm_of unimod_of absComm_of`.
-/
theorem twOrbComm_of (h : OrbProper) : TwOrbComm := twOrbComm gLTop_of extCont_of twCent_of h haarComm_of unimod_of absComm_of

/- English proof (translation)
The claim follows from `orbComm (twOrbComm_of h) untwist_of`.
-/
theorem orbComm_of (h : OrbProper) : OrbComm := orbComm (twOrbComm_of h) untwist_of

end UpperTheory.V.Z.Tf.Orb
