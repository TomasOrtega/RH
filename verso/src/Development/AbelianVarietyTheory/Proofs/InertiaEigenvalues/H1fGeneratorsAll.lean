import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratedLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem h1f_generators_of_record : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm13 D := by
  intro D l _ K LL _ T _
  exact GlobalTheory.T.h1f_generated_lattice l (D.loc l) (D.locA l) (D.locT l) K LL T

end GlobalTheory
