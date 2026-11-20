import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.Ii

noncomputable section

universe u v

namespace PI.KoszulExact

section General

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem contract_pow_eq_zero (N : Submodule R M) (f : Module.Dual R M) (hf : ∀ m ∈ N, f m = 0) :
    ∀ (j : ℕ) (x : ExteriorAlgebra R M), x ∈ (N.map (ExteriorAlgebra.ι R)) ^ j →
      CliffordAlgebra.contractLeft f x = 0 := by
  intro j
  induction j with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.mem_one] at hx
    obtain ⟨y, rfl⟩ := hx
    exact CliffordAlgebra.contractLeft_algebraMap _ f y
  | succ j ih =>
    intro x hx
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨m, hm, rfl⟩ := ha
      rw [CliffordAlgebra.contractLeft_ι_mul, hf m hm, ih b hb, zero_smul, mul_zero, sub_zero]
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]

end General

section Koszul

variable {R : Type u} [CommRing R] {D : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem Li_eq_map (R : Type u) [CommRing R] (D : ℕ) (i : ℕ) :
    Li R D i = (Submodule.span R ((fun k : Fin D => (Pi.single k (1 : R) : Fin D → R)) ''
      {k : Fin D | (k : ℕ) < i})).map (ExteriorAlgebra.ι R) := by
  rw [Submodule.map_span, Set.image_image]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem form_single (s : Fin D → R) (k : Fin D) : form s (Pi.single k 1) = s k := by
  simp [form, Pi.single_apply]

end Koszul

end PI.KoszulExact
