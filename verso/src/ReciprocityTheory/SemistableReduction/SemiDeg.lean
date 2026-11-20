import ReciprocityTheory.SemistableReduction.SemiDegZA
import ReciprocityTheory.SemistableReduction.SemiDegA
import ReciprocityTheory.SemistableReduction.SemiDegB
import ReciprocityTheory.SemistableReduction.SemiDegC
import ReciprocityTheory.SemistableReduction.SemiDegD

namespace ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem semiDeg_holds (hD : DegAddStatement) : SemiPointStatement :=
  SemiPt.semiPoint_of wittBasis_holds latDegBasis_holds integralIndex_holds selfDualIndex_holds
    (gradedExt_holds latDegBasis_holds hD) absDet_holds

end ReciprocityTheory.MultiplicativeHeights
