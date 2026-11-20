import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.ContractPowSuccMem

noncomputable section

universe u

namespace PI.KoszulExact

variable {R : Type u} [CommRing R] {D : ℕ}

def Dc (R : Type u) [CommRing R] {D : ℕ} (i : Fin D) (p q : ℕ) (x : ExteriorAlgebra R (Fin D → R)) :
    Prop :=
  ∃ a ∈ Li R D i ^ p, ∃ b ∈ Li R D i ^ q, x = a + eb R i * b

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem Dc_zero (i : Fin D) (p q : ℕ) : Dc R i p q 0 :=
  ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem Dc_add (i : Fin D) (p q : ℕ) (x y : ExteriorAlgebra R (Fin D → R))
    (hx : Dc R i p q x) (hy : Dc R i p q y) : Dc R i p q (x + y) := by
  obtain ⟨a1, ha1, b1, hb1, rfl⟩ := hx
  obtain ⟨a2, ha2, b2, hb2, rfl⟩ := hy
  refine ⟨a1 + a2, Submodule.add_mem _ ha1 ha2, b1 + b2, Submodule.add_mem _ hb1 hb2, ?_⟩
  rw [mul_add]
  abel

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem Dc_smul (i : Fin D) (p q : ℕ) (r : R) (x : ExteriorAlgebra R (Fin D → R))
    (hx : Dc R i p q x) : Dc R i p q (r • x) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨r • a, Submodule.smul_mem _ _ ha, r • b, Submodule.smul_mem _ _ hb,
    by rw [smul_add, mul_smul_comm]⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eb_mul_swap (k i : Fin D) : eb R k * eb R i = -(eb R i * eb R k) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eb_mul_self (i : Fin D) : eb R i * eb R i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eb_mem_Li (k : Fin D) (i : ℕ) (hk : (k : ℕ) < i) : eb R k ∈ Li R D i :=
  Submodule.subset_span ⟨k, hk, rfl⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem one_mem_pow_zero (i : ℕ) : (1 : ExteriorAlgebra R (Fin D → R)) ∈ Li R D i ^ 0 := by
  rw [pow_zero]
  exact Submodule.mem_one.2 ⟨1, map_one _⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Supply the required witnesses or components. Establish an intermediate fact. Substitute using the available equality. Supply the required witnesses or components. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem decomp (i : Fin D) : ∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)),
    x ∈ Li R D ((i : ℕ) + 1) ^ (j + 1) →
      ∃ a ∈ Li R D i ^ (j + 1), ∃ b ∈ Li R D i ^ j, x = a + eb R i * b := by
  intro j
  induction j with
  | zero =>
    intro x hx
    rw [zero_add, pow_one] at hx
    show Dc R i 1 0 x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
      by_cases hki : (k : ℕ) < i
      · exact ⟨eb R k, by rw [pow_one]; exact eb_mem_Li k _ hki, 0, Submodule.zero_mem _, by simp⟩
      · have : k = i := Fin.ext (by omega)
        subst this
        exact ⟨0, Submodule.zero_mem _, 1, one_mem_pow_zero _, by simp⟩
    | zero => exact Dc_zero i 1 0
    | add x y _ _ hx hy => exact Dc_add i 1 0 x y hx hy
    | smul r x _ hx => exact Dc_smul i 1 0 r x hx
  | succ j ih =>
    intro x hx
    rw [pow_succ'] at hx
    show Dc R i (j + 2) (j + 1) x
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      obtain ⟨a2, ha2, b2, hb2, rfl⟩ := ih n hn
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, hk, rfl⟩ := hy
        have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
        by_cases hki : (k : ℕ) < i
        · refine ⟨eb R k * a2, ?_, -(eb R k * b2), ?_, ?_⟩
          · rw [pow_succ']
            exact Submodule.mul_mem_mul (eb_mem_Li k _ hki) ha2
          · rw [pow_succ']
            exact Submodule.neg_mem _ (Submodule.mul_mem_mul (eb_mem_Li k _ hki) hb2)
          · rw [mul_add, ← mul_assoc, eb_mul_swap, neg_mul, mul_assoc, mul_neg]
        · have : k = i := Fin.ext (by omega)
          subst this
          refine ⟨0, Submodule.zero_mem _, a2, ha2, ?_⟩
          rw [mul_add, ← mul_assoc, eb_mul_self, zero_mul, add_zero, zero_add]
      | zero => rw [zero_mul]; exact Dc_zero i _ _
      | add x y _ _ hx hy => rw [add_mul]; exact Dc_add i _ _ _ _ hx hy
      | smul r x _ hx => rw [smul_mul_assoc]; exact Dc_smul i _ _ r _ hx
    · intro x y hx hy
      exact Dc_add i _ _ x y hx hy

end PI.KoszulExact
