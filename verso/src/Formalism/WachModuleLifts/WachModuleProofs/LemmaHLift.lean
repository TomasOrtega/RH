import Formalism.WachModuleLifts.Statement

namespace Formalism.CL

open Finset

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem legendreBound : Legendre := by
  unfold Legendre
  intro p hp m
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have hq : 0 < q := by have := hp.out.one_lt; omega
  have key : q * padicValNat (q + 1) m.factorial ≤ m := by
    have h := sub_one_mul_padicValNat_factorial (p := q + 1) m
    rw [Nat.add_sub_cancel] at h
    omega
  have hN : (m + padicValNat (q + 1) m.factorial) * q ≤ m * (q + 1) := by nlinarith [key]
  push_cast
  try simp only [add_sub_cancel_right]
  rw [le_div_iff₀ (by exact_mod_cast hq)]
  exact_mod_cast hN

end Formalism.CL
