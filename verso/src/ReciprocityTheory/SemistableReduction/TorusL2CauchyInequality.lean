import ReciprocityTheory.SemistableReduction.SJCore
import ReciprocityTheory.SemistableReduction.SjHolds
import ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact
import ReciprocityTheory.SemistableReduction.HeightLowerBound
import ReciprocityTheory.SemistableReduction.IntCores
import ReciprocityTheory.SemistableReduction.TorusMean
import ReciprocityTheory.SemistableReduction.TorusLex
import ReciprocityTheory.SemistableReduction.GramOfLinearOrder
import ReciprocityTheory.SemistableReduction.SphereTorus

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sphereLinLog : SphereLinLogStatement := sjCore_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sj : SJStatement := sj_holds sphereLinLog

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sphereLogIntegrable : SphereLogIntegrableStatement := sphereLogIntegrable_holds sj

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gauss_height_additivity : HeightAdditiveStatement := gauss_height_add_of_sphere sphereLogIntegrable

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sphere_height_lower_bound : HeightLowerBoundStatement := heightLowerBound_of_sj_of_sphereLogIntegrable sj sphereLogIntegrable

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torusMeanBasic : TorusMeanBasicStatement := torusMean_holds.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torusCoeff : TorusCoeffStatement := torusMean_holds.2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torusLex : TorusLexStatement := (torusLex_holds torusMeanBasic torusCoeff).1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torus_l2_cauchy_inequality : TorusL2Cauchy := (torusLex_holds torusMeanBasic torusCoeff).2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gram : GramStatement := gram_holds torusMeanBasic torusLex torus_l2_cauchy_inequality

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sphereLeTorus : SphereLeTorusStatement := sphereTorus_holds sphereLogIntegrable torusMeanBasic

end ReciprocityTheory.MultiplicativeHeights.Closed
