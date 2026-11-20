import Mathlib
import Formalism.PeriodIntegrals.OddDualWeyl
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.OddDualWeylFactorization

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oddDualWeyl {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    PI.OddDualWeyl.OddFact (K := K) O m lam :=
  PI.OddDualWeyl.odd_dual_weyl_factorization O m lam
