import Formalism.LocalRingCardinality.HostCls

open Formalism.HC

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R) {p : ℕ}

/- English proof (translation)
Introduce `e` and use `((primeClass_eq_signal_iff H.toHostRaw).1 e).2.2.2.1 h`.
-/
theorem cls_ne_signal_of_jacobi (h : jacobiSym (-(H.d : ℤ)) p = 1) : H.cls p ≠ .signal := fun e =>
  ((primeClass_eq_signal_iff H.toHostRaw).1 e).2.2.2.1 h

/- English proof (translation)
Introduce `e` and use `((primeClass_eq_inert_iff H.toHostRaw).1 e).2.2.2.1 h`.
-/
theorem primeClass_ne_of_jacobi_one (h : jacobiSym (-(H.d : ℤ)) p = 1) : H.cls p ≠ .inertClass := fun e =>
  ((primeClass_eq_inert_iff H.toHostRaw).1 e).2.2.2.1 h

/- English proof (translation)
Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality. Establish `e : H.cls 2 = .ram2` using `primeClass_two H.toHostRaw`. Rewrite using `[e]`. Simplify using the standard rewrite rules.

Establish `hj` using `H.split_small p hp h2 h`. Introduce and unpack `(e | e)`. Conclude with `H.cls_ne_signal_of_jacobi hj e`. Conclude with `H.primeClass_ne_of_jacobi_one hj e`.
-/
theorem not_inert_of_le_splitBound (hp : p.Prime) (h : p ≤ H.splitBound) :
    ¬ (H.cls p = .signal ∨ H.cls p = .inertClass) := by
  by_cases h2 : p = 2
  · subst h2
    have e : H.cls 2 = .ram2 := primeClass_two H.toHostRaw
    rw [e]
    simp
  · have hj := H.split_small p hp h2 h
    rintro (e | e)
    · exact H.cls_ne_signal_of_jacobi hj e
    · exact H.primeClass_ne_of_jacobi_one hj e

/- English proof (translation)
The claim follows from `lt_of_not_ge fun hle => H.not_inert_of_le_splitBound hp hle h`.
-/
theorem splitBound_lt_of_inert (hp : p.Prime) (h : H.cls p = .signal ∨ H.cls p = .inertClass) : H.splitBound < p :=
  lt_of_not_ge fun hle => H.not_inert_of_le_splitBound hp hle h

/- English proof (translation)
Establish `h1` using `H.splitBound_lt_of_inert hp h`. Establish `h4 : p ≠ 4` using `by rintro rfl; exact absurd hp (by norm_num)`. Use linear arithmetic over natural numbers and integers.
-/
theorem five_le_of_inert (hp : p.Prime) (h3 : 3 ≤ H.splitBound) (h : H.cls p = .signal ∨ H.cls p = .inertClass) : 5 ≤ p := by
  have h1 := H.splitBound_lt_of_inert hp h
  have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
  omega

/- English proof (translation)
Distinguish the cases in `hs : p ∈ H.small`. Conclude with `Or.inr hs`. Establish `h2 : p ≠ 2` using `fun e => hs (e ▸ H.two_mem_small)`. Conclude with `Or.inl ((primeClass_eq_splitK_iff H.toHostRaw).2 ⟨hs, hq, hd, H.split_small p hp h2 h⟩)`.
-/
theorem cls_splitK_or_small (hp : p.Prime) (h : p ≤ H.splitBound) (hq : p ≠ H.q) (hd : p ≠ H.d) :
    H.cls p = .splitK ∨ p ∈ H.small := by
  by_cases hs : p ∈ H.small
  · exact Or.inr hs
  · have h2 : p ≠ 2 := fun e => hs (e ▸ H.two_mem_small)
    exact Or.inl ((primeClass_eq_splitK_iff H.toHostRaw).2 ⟨hs, hq, hd, H.split_small p hp h2 h⟩)

end Formalism.BasicNotions.Host
