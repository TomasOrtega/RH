import Mathlib

universe u_1

namespace GlobalTheory.ProductOfFnSingle

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem prod_ofFn_eq_single {M : Type u_1} [inst : Monoid M] {d : ℕ} (g : Fin d → M) (j : Fin d)
    (h : ∀ (i : Fin d), i ≠ j → g i = (1 : M)) : List.prod (List.ofFn g) = g j := by
  induction d with
  | zero => exact j.elim0
  | succ d ih =>
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      have hrest : List.prod (List.ofFn fun i : Fin d => g i.succ) = 1 := by
        apply List.prod_eq_one
        intro x hx
        simp only [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact h _ (Fin.succ_ne_zero i)
      rw [hrest, mul_one]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
      rw [h 0 (fun e => hj e.symm), one_mul]
      exact ih (fun i => g i.succ) j' (fun i hi => h _ (fun e => hi (Fin.succ_injective _ e)))

end GlobalTheory.ProductOfFnSingle
