import Mathlib

namespace GlobalTheory.PowerBound

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => set I := Ideal.span {a} ⊔ Ideal.span {d} with hI`. Establish `haI : a ^ (n + 1) ∈ I ^ (n + 1)` using `Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Ideal.mul_sup, mul_left_comm]`. Use `_ ≤ Ideal.span {a ^ (n + 1 + 1)} ⊔ Ideal.span {d} * I ^ (n + 1) := by`. Apply `sup_le` to reduce the goal to its premises. Rewrite using `[hI, Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton, ← pow_succ']`. Apply `sup_le_sup_left` to reduce the goal to its premises.

Conclude with `Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 haI)`. Rewrite using `[← pow_succ']`. Conclude with `le_sup_right`.
-/
theorem pow_le {A : Type} [CommRing A] (a d : A) (n : ℕ) :
    (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + 1) ≤
      Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * (Ideal.span {a} ⊔ Ideal.span {d}) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set I := Ideal.span {a} ⊔ Ideal.span {d} with hI
    have haI : a ^ (n + 1) ∈ I ^ (n + 1) :=
      Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) _
    calc I ^ (n + 1 + 1) = I * I ^ (n + 1) := pow_succ' I (n + 1)
      _ ≤ I * (Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * I ^ n) := Ideal.mul_mono_right ih
      _ = I * Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * (I * I ^ n) := by
          rw [Ideal.mul_sup, mul_left_comm]
      _ ≤ Ideal.span {a ^ (n + 1 + 1)} ⊔ Ideal.span {d} * I ^ (n + 1) := by
          apply sup_le
          · rw [hI, Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton, ← pow_succ']
            apply sup_le_sup_left
            exact Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 haI)
          · rw [← pow_succ']
            exact le_sup_right

/- English proof (translation)
Introduce `A _ a d n x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 (pow_le a d n hx)`. Take `⟨u, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Take `⟨w, hw, rfl⟩` from `Ideal.mem_span_singleton_mul.1 hz`. Conclude with `⟨u, w, hw, by ring⟩`.
-/
theorem main : ∀ {A : Type} [inst : CommRing A] (a d : A) (n : ℕ) {x : A},
    x ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + (1 : ℕ)) →
      ∃ (u : A), ∃ w ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n, x = a ^ (n + (1 : ℕ)) * u + d * w := by
  intro A _ a d n x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (pow_le a d n hx)
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hz
  exact ⟨u, w, hw, by ring⟩

end GlobalTheory.PowerBound
