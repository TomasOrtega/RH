import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.UniqGapOfBmu
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGapAlt

namespace CompanionTheory.Lime.BM

open Formalism.BasicNotions

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uniqGap_holds : UniqGap := CompanionTheory.Bmu.besselMapUniqGap

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ampUnif_holds : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif := ampUnif CompanionTheory.Bmu.besselMapUniqGap

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wuDecayOfGap_holds' : Formalism.L2.SG.Pf.WuDecayOfGap := wuDecayOfGap CompanionTheory.Bmu.besselMapUniqGap

end CompanionTheory.Lime.BM
