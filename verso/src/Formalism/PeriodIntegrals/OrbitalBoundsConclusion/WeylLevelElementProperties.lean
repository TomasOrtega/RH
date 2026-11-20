import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylConjugationFixedColumn.ReflectionScalarDualIsotropic

/- English proof (translation)
The claim follows from `PI.IsotropicReflections.isotropic_reflection_properties`.
-/
theorem weyl_level_element_properties' : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts :=
  PI.IsotropicReflections.isotropic_reflection_properties
