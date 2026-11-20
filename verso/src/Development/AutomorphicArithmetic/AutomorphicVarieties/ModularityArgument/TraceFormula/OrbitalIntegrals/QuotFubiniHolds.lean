import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniOf
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper

namespace UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
The claim follows from `UpperTheory.ConvolutionTheory.Loc.orbProper`.
-/
theorem orbProper_holds : OrbProper := UpperTheory.ConvolutionTheory.Loc.orbProper

/- English proof (translation)
The claim follows from `gLTop_of`.
-/
theorem gLTop_holds : GLTop := gLTop_of

/- English proof (translation)
The claim follows from `extCont_of`.
-/
theorem extCont_holds : ExtCont := extCont_of

/- English proof (translation)
The claim follows from `centComm_of`.
-/
theorem centComm_holds : CentComm := centComm_of

/- English proof (translation)
The claim follows from `twCent_of`.
-/
theorem twCent_holds : TwCent := twCent_of

/- English proof (translation)
The claim follows from `haarComm_of`.
-/
theorem haarComm_holds : HaarComm := haarComm_of

/- English proof (translation)
The claim follows from `quotIndep_of`.
-/
theorem quotIndep_holds : QuotIndep := quotIndep_of

/- English proof (translation)
The claim follows from `normEx_of`.
-/
theorem normEx_holds : NormEx := normEx_of

/- English proof (translation)
The claim follows from `quotInt_of`.
-/
theorem quotInt_holds : QuotInt := quotInt_of

/- English proof (translation)
The claim follows from `convTest_of`.
-/
theorem convTest_holds : ConvTest := convTest_of

/- English proof (translation)
The claim follows from `untwist_of`.
-/
theorem untwist_holds : Untwist := untwist_of

/- English proof (translation)
The claim follows from `twOrbLin_of orbProper_holds`.
-/
theorem twOrbLin_holds : TwOrbLin := twOrbLin_of orbProper_holds

/- English proof (translation)
The claim follows from `orbLin_of orbProper_holds`.
-/
theorem orbLin_holds : OrbLin := orbLin_of orbProper_holds

/- English proof (translation)
The claim follows from `twOrbComm_of orbProper_holds`.
-/
theorem twOrbComm_holds : TwOrbComm := twOrbComm_of orbProper_holds

/- English proof (translation)
The claim follows from `orbComm_of orbProper_holds`.
-/
theorem orbComm_holds : OrbComm := orbComm_of orbProper_holds

end UpperTheory.V.Z.Tf.Orb
