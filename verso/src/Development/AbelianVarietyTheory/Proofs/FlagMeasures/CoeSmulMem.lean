import Mathlib

namespace GlobalTheory.IntegralMultiple

open NumberField

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Use `⟨y, hy, ⟨y • c, hint⟩, ?_⟩` and prove the remaining obligations. Simplify using `[zsmul_eq_mul]`.
-/
theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ a : 𝓞 E, (a : E) = (m : E) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y, hy, ⟨y • c, hint⟩, ?_⟩
  simp [zsmul_eq_mul]

/- English proof (translation)
Use `Λ.smul_mem r hv` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul E r v]`. Then use the resulting hypothesis.
-/
theorem coe_smul_mem {E : Type} [Field E] [NumberField E] {j : ℕ}
    (Λ : Submodule (𝓞 E) (Fin j → E)) (r : 𝓞 E) {v : Fin j → E} (hv : v ∈ Λ) :
    (r : E) • v ∈ Λ := by
  have := Λ.smul_mem r hv
  rwa [← algebraMap_smul E r v] at this

/- English proof (translation)
Introduce `E _ _ j Λ hΛ x`. Set `S : Submodule E (Fin j → E)` to `{ carrier := {x | ∃ n : ℤ, n ≠ 0 ∧ (n : E) • x ∈ Λ} add_mem' := by`. Introduce and unpack `a b ⟨n, hn, ha⟩ ⟨m, hm, hb⟩`. Use `⟨n * m, mul_ne_zero hn hm, ?_⟩` and prove the remaining obligations. Establish `h1` using `coe_smul_mem Λ (m : 𝓞 E) ha`.

Establish `h2` using `coe_smul_mem Λ (n : 𝓞 E) hb`. Use `Λ.add_mem h1 h2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [smul_add, smul_smul, map_intCast, Int.cast_mul]`. Use `push_cast`. Rewrite using `[mul_comm (m : E) (n : E)]`.

Use the proof step `zero_mem' := ⟨1, one_ne_zero, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c v ⟨n, hn, hv⟩`. Take `⟨m, hm, a, ha⟩` from `exists_int_mul_integral c`. Use `⟨m * n, mul_ne_zero hm hn, ?_⟩` and prove the remaining obligations.

Establish `h` using `coe_smul_mem Λ a hv`. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_smul, smul_smul, ha]`. Use `push_cast`. Use `ring_nf }`.

Establish `hle : Submodule.span E (Λ : Set (Fin j → E)) ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce `v hv`. Conclude with `⟨1, one_ne_zero, by simpa using hv⟩`. Rewrite `hle` using `[hΛ.span_eq_top]`.

Conclude with `hle Submodule.mem_top`.
-/
theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {j : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin j → E)),
    Submodule.IsLattice E Λ → ∀ (x : Fin j → E), ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ (↑n : E) • x ∈ Λ := by
  intro E _ _ j Λ hΛ x
  let S : Submodule E (Fin j → E) :=
    { carrier := {x | ∃ n : ℤ, n ≠ 0 ∧ (n : E) • x ∈ Λ}
      add_mem' := by
        rintro a b ⟨n, hn, ha⟩ ⟨m, hm, hb⟩
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        have h1 := coe_smul_mem Λ (m : 𝓞 E) ha
        have h2 := coe_smul_mem Λ (n : 𝓞 E) hb
        convert Λ.add_mem h1 h2 using 1
        simp only [smul_add, smul_smul, map_intCast, Int.cast_mul]
        push_cast
        rw [mul_comm (m : E) (n : E)]
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c v ⟨n, hn, hv⟩
        obtain ⟨m, hm, a, ha⟩ := exists_int_mul_integral c
        refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
        have h := coe_smul_mem Λ a hv
        convert h using 1
        rw [smul_smul, smul_smul, ha]
        push_cast
        ring_nf }
  have hle : Submodule.span E (Λ : Set (Fin j → E)) ≤ S := by
    rw [Submodule.span_le]
    intro v hv
    exact ⟨1, one_ne_zero, by simpa using hv⟩
  rw [hΛ.span_eq_top] at hle
  exact hle Submodule.mem_top

end GlobalTheory.IntegralMultiple
