import Mathlib

namespace GlobalTheory.IntegralMultiple

open NumberField

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ a : 𝓞 E, (a : E) = (m : E) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y, hy, ⟨y • c, hint⟩, ?_⟩
  simp [zsmul_eq_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem coe_smul_mem {E : Type} [Field E] [NumberField E] {j : ℕ}
    (Λ : Submodule (𝓞 E) (Fin j → E)) (r : 𝓞 E) {v : Fin j → E} (hv : v ∈ Λ) :
    (r : E) • v ∈ Λ := by
  have := Λ.smul_mem r hv
  rwa [← algebraMap_smul E r v] at this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Put the polynomial expressions in normal form. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
