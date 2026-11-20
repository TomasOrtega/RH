import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExtProof
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ImportsAlt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfNormLeTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PaThDiffLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement

namespace ReciprocityTheory.ChartRestriction.G.I2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gSup_holds : GSupStatement := gSup Ext.all.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem propA_holds : PropAStatement := propA Ext.all.1 Ext.all.2.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dim_holds : DimStatement := dim

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem split_holds : SplitStatement := split Ext.all

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem char_holds : CharStatement := char Ext.all

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem J_holds : JStatement :=
  jOf Ext.all split_holds char_holds (colTorus Ext.all propA_holds gSup_holds)
    (colAbel Ext.all propA_holds gSup_holds) (colEmpty Ext.all propA_holds gSup_holds)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem N_holds : NStatement := lemmaN dim_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem I_holds : IStatement := iOf J_holds N_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem T_holds : TStatement := tOf Ext.all split_holds gSup_holds dim_holds

end ReciprocityTheory.ChartRestriction.G.I2
