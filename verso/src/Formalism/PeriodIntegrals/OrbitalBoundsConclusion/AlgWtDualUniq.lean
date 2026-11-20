import Mathlib
import Formalism.LocalToGlobal.AdelicCompactOpens.UniROfUniRT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualUniqueness.Imports

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algebraic_weight_dual_unique (L : Type) [Field L] [NumberField L] [NumberField.IsCMField L] (n : ℕ) : Formalism.L2.Props.DualUnique L n :=
  PI.UnitaryGroupMassFormula.AlgWtDualUniq.main L n
