import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TermIdIffInSOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMTraceOnto

noncomputable section

open NumberField Formalism.BasicNotions

namespace PI.UnitaryGroupMassFormula.IdCellInSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem traceOne_holds (D : D7) : TraceOne D := by
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE

  have hgal := (D.host.der.conj_iff D.host.φ₀ ((NumberField.IsCMField.complexConj D.host.E).restrictScalars ℚ)).mp (fun x =>
    NumberField.ComplexEmbedding.IsConj.eq (NumberField.IsCMField.isConj_complexConj D.host.E D.host.φ₀) x)
  have hc : ∀ x : D.host.E, D.host.conj x = star x := by
    intro x
    unfold Formalism.HC.HostRaw.conj
    rw [← hgal, MulEquiv.symm_apply_apply]
    rfl
  have hU : PI.IsCMUnram D.host.E := by
    refine ⟨?_, ?_, ?_⟩
    · infer_instance
    · intro ψ a
      exact NumberField.ComplexEmbedding.IsConj.eq (NumberField.IsCMField.isConj_complexConj D.host.E ψ) a
    · intro P hP
      have hne : P ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField D.host.E)
      have h := D.host.der.unramEF P hP.isPrime hne
      push_neg at h
      obtain ⟨x, hx⟩ := h
      refine ⟨x, D.host.conj • x, ?_, ?_⟩
      · rw [← hc]
        rfl
      · intro hmem
        apply hx
        rw [← neg_sub]
        exact P.neg_mem hmem
  obtain ⟨x, y, hy, hxy⟩ := traceSurjective_holds D.host.E hU 1 (by simp)
  refine ⟨x, ?_⟩
  rw [← hy]
  exact_mod_cast congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hxy

end PI.UnitaryGroupMassFormula.IdCellInSW
