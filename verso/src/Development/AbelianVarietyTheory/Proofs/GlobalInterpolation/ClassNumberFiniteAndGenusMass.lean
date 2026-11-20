import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumInvCardStabEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeStabilizerDoubleCosetsClassRestMassStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassNumberMass

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem classFin_and_classMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  intro D
  refine ⟨fun W hW hsig => ?_, fun W hW hsig n g hcov hdisj => ?_⟩
  · obtain ⟨n, g, hcov, hdisj, _⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W hW hsig
    exact ⟨n, g, hcov, hdisj⟩
  · obtain ⟨m, g', hcov', hdisj', hsum⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W hW hsig
    rw [← hsum]
    exact GlobalTheory.WeightedDoubleCoset.sum_inv_card_stab_eq _ _ _ n m g g' hcov hdisj hcov' hdisj'

end GlobalTheory.ClassNumberMass
