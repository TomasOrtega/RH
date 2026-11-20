import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHensSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PValLiftB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFibExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSecGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PClopenAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PWtVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycRes
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycAll
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PNwtOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PullHQComp

namespace UpperTheory.Gal.Mod

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtVal_holds : WtVal := by
  exact wtVal fibExt secGen (clopenAt resClosed hensSplit)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cycAll_holds : CycAll := by
  exact cycAll resClosed valLiftB (cycRes wtVal_holds) (cycExt fibExt)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem esPt_holds : ESPt := esPt cycAll_holds

end UpperTheory.Gal.Mod
