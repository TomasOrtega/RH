import Mathlib

namespace GlobalTheory.SmoothEvaluation

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem main : ∀ {A R : Type} [inst : CommRing A] [inst_1 : CommRing R] [inst_2 : Algebra A R] {r : ℕ} (b : Fin r → R), (∀ (f : R), ∃! cf : Fin r → A, f = ∑ i : Fin r, (Algebra.algebraMap A R : A → R) (cf i) * b i) → ∃ (e : Module.Basis (Fin r) A R), ∀ (i : Fin r), (e : Fin r → R) i = b i := by
  intro A R _ _ _ r b h
  have hli : LinearIndependent A b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨c, _, hc⟩ := h 0
    have h1 := hc g (by simp only [Algebra.smul_def] at hg; exact hg.symm)
    have h2 := hc 0 (by simp)
    intro i
    rw [h1, ← h2]
    rfl
  have hsp : ⊤ ≤ Submodule.span A (Set.range b) := by
    intro f _
    obtain ⟨c, hc, _⟩ := h f
    rw [hc]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

end GlobalTheory.SmoothEvaluation
