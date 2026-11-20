import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import ReciprocityTheory.SemistableReduction.TorusLexA
import ReciprocityTheory.SemistableReduction.TorusLexC

namespace ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem torusLex_holds (hBasic : TorusMeanBasicStatement) (hCoeff : TorusCoeffStatement) :
    TorusLexStatement ∧ TorusL2Cauchy :=
  ⟨TorusLexOrder.torusLex_of hBasic hCoeff, TorusLexOrder.torus_l2_cauchy_of_basic hBasic⟩

end ReciprocityTheory.MultiplicativeHeights
