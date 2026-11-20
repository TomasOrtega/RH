import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TermIdIffInSOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMTraceOnto

noncomputable section

open NumberField Formalism.BasicNotions

namespace PI.UnitaryGroupMassFormula.IdCellInSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE`. Establish `hgal` using `(D.host.der.conj_iff D.host.φ₀ ((NumberField.IsCMField.complexConj D.host.E).restrictScalars ℚ)).mp (fun x => NumberField.ComplexEmbedding.IsConj.eq (NumberField.IsCMField.isConj_complexConj D.host.E D.host.φ₀) x)`. Establish `hc : ∀ x : D.host.E, D.host.conj x = star x`. Introduce `x`. Unfold `Formalism.HC.HostRaw.conj`.

Rewrite using `[← hgal, MulEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hU : PI.IsCMUnram D.host.E`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `infer_instance`.

Introduce `ψ a`. Conclude with `NumberField.ComplexEmbedding.IsConj.eq (NumberField.IsCMField.isConj_complexConj D.host.E ψ) a`. Introduce `P hP`. Establish `hne : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField D.host.E)`. Establish `h` using `D.host.der.unramEF P hP.isPrime hne`.

Use `push_neg at h`. Take `⟨x, hx⟩` from `h`. Use `⟨x, D.host.conj • x, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Both sides reduce to the same expression.

Introduce `hmem`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← neg_sub]`. Conclude with `P.neg_mem hmem`. Take `⟨x, y, hy, hxy⟩` from `traceSurjective_holds D.host.E hU 1 (by simp)`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Conclude with `congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hxy` after adjusting the coercions.
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
