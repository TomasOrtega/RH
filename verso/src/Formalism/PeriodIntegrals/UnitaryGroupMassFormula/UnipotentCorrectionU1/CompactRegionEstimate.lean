import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompRB

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the hypotheses and unpack their components. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem compact_region_estimate : CompR := by
  intro k r ψ h cost n C₀ hψ hh hb H
  obtain ⟨K, _, hK⟩ := CRH.main ψ h cost n C₀ hψ hh hb (by
      rintro w ⟨u, v, hu, hv, hl, rfl⟩ hne g hg
      have hne' : u ++ v ≠ [] := by
        rintro h0
        rw [List.append_eq_nil_iff] at h0
        obtain ⟨rfl, rfl⟩ := h0
        exact hne (by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR])
      have key := H u v hu hv hl hne' g hg
      rwa [P.BetaSesquilinearity.dLR_eq, Real.rpow_natCast, CRH.cs_LR] at key) n 0
  refine ⟨K, fun u v hu hv hl g hg => ?_⟩
  have key := hK (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v) ⟨u, v, hu, hv, hl, rfl⟩
    (by simpa [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR] using hl) g hg
  rw [P.BetaSesquilinearity.dLR_eq, zero_add, Real.rpow_natCast, CRH.cs_LR]
  simpa [iteratedDeriv_zero] using key

end PI.UnitaryCorollaryDerivatives
