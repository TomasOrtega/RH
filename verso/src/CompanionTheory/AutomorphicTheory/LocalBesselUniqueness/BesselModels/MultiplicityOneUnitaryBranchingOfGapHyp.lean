import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.UniqGapOfBmu
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGapAlt

namespace CompanionTheory.Lime.BM

open Formalism.BasicNotions

/- English proof (translation)
The claim follows from `CompanionTheory.Bmu.besselMapUniqGap`.
-/
theorem uniqGap_holds : UniqGap := CompanionTheory.Bmu.besselMapUniqGap

/- English proof (translation)
The claim follows from `ampUnif CompanionTheory.Bmu.besselMapUniqGap`.
-/
theorem ampUnif_holds : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif := ampUnif CompanionTheory.Bmu.besselMapUniqGap

/- English proof (translation)
The claim follows from `wuDecayOfGap CompanionTheory.Bmu.besselMapUniqGap`.
-/
theorem wuDecayOfGap_holds' : Formalism.L2.SG.Pf.WuDecayOfGap := wuDecayOfGap CompanionTheory.Bmu.besselMapUniqGap

end CompanionTheory.Lime.BM
