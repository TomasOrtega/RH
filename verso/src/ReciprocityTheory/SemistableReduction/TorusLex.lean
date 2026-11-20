import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import ReciprocityTheory.SemistableReduction.TorusLexA
import ReciprocityTheory.SemistableReduction.TorusLexC

namespace ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
Assemble the required witnesses or components as `⟨TorusLexOrder.torusLex_of hBasic hCoeff, TorusLexOrder.torus_l2_cauchy_of_basic hBasic⟩`.
-/
theorem torusLex_holds (hBasic : TorusMeanBasicStatement) (hCoeff : TorusCoeffStatement) :
    TorusLexStatement ∧ TorusL2Cauchy :=
  ⟨TorusLexOrder.torusLex_of hBasic hCoeff, TorusLexOrder.torus_l2_cauchy_of_basic hBasic⟩

end ReciprocityTheory.MultiplicativeHeights
