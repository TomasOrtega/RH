import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolyBB

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem polynomial_bound : PolyB := by
  intro k r κ P hP
  obtain ⟨hsmooth, hbound⟩ := pb_poly hP
  refine ⟨hsmooth, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hbound n
  refine ⟨C, fun u v hu hv hn g hg => ?_⟩
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
  have hw : ∀ x ∈ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v, B.unitLie k r x.2 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
      exact hu X hX
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
      exact hv X hX
  have hlen : (Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v).length ≤ n := by
    simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR] using hn
  simpa using hC _ hw hlen g hg

end PI.UnitaryCorollaryDerivatives
