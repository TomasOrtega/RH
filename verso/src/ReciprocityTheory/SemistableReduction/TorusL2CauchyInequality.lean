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
The claim follows from `sjCore_holds`.
-/
theorem sphereLinLog : SphereLinLogStatement := sjCore_holds

/- English proof (translation)
The claim follows from `sj_holds sphereLinLog`.
-/
theorem sj : SJStatement := sj_holds sphereLinLog

/- English proof (translation)
The claim follows from `sphereLogIntegrable_holds sj`.
-/
theorem sphereLogIntegrable : SphereLogIntegrableStatement := sphereLogIntegrable_holds sj

/- English proof (translation)
The claim follows from `gauss_height_add_of_sphere sphereLogIntegrable`.
-/
theorem gauss_height_additivity : HeightAdditiveStatement := gauss_height_add_of_sphere sphereLogIntegrable

/- English proof (translation)
The claim follows from `heightLowerBound_of_sj_of_sphereLogIntegrable sj sphereLogIntegrable`.
-/
theorem sphere_height_lower_bound : HeightLowerBoundStatement := heightLowerBound_of_sj_of_sphereLogIntegrable sj sphereLogIntegrable

/- English proof (translation)
The claim follows from `torusMean_holds.1`.
-/
theorem torusMeanBasic : TorusMeanBasicStatement := torusMean_holds.1

/- English proof (translation)
The claim follows from `torusMean_holds.2`.
-/
theorem torusCoeff : TorusCoeffStatement := torusMean_holds.2

/- English proof (translation)
The claim follows from `(torusLex_holds torusMeanBasic torusCoeff).1`.
-/
theorem torusLex : TorusLexStatement := (torusLex_holds torusMeanBasic torusCoeff).1

/- English proof (translation)
The claim follows from `(torusLex_holds torusMeanBasic torusCoeff).2`.
-/
theorem torus_l2_cauchy_inequality : TorusL2Cauchy := (torusLex_holds torusMeanBasic torusCoeff).2

/- English proof (translation)
The claim follows from `gram_holds torusMeanBasic torusLex torus_l2_cauchy_inequality`.
-/
theorem gram : GramStatement := gram_holds torusMeanBasic torusLex torus_l2_cauchy_inequality

/- English proof (translation)
The claim follows from `sphereTorus_holds sphereLogIntegrable torusMeanBasic`.
-/
theorem sphereLeTorus : SphereLeTorusStatement := sphereTorus_holds sphereLogIntegrable torusMeanBasic

end ReciprocityTheory.MultiplicativeHeights.Closed
