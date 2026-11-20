import Formalism.WachModuleLifts.Statement

namespace Formalism.CL

open Finset

/- English proof (translation)
Unfold `Legendre`. Introduce `p hp m`. Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, by have := hp.out.one_lt; omega⟩`. Establish `hq : 0 < q` using `by have := hp.out.one_lt; omega`. Establish `key : q * padicValNat (q + 1) m.factorial ≤ m`.

Establish `h` using `sub_one_mul_padicValNat_factorial (p := q + 1) m`. Rewrite `h` using `[Nat.add_sub_cancel]`. Use linear arithmetic over natural numbers and integers. Establish `hN : (m + padicValNat (q + 1) m.factorial) * q ≤ m * (q + 1)` using `by nlinarith [key]`. Use `push_cast`.

Apply the tactic sequence `try simp only [add_sub_cancel_right]`. Rewrite using `[le_div_iff₀ (by exact_mod_cast hq)]`. Conclude with `hN` after adjusting the coercions.
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
