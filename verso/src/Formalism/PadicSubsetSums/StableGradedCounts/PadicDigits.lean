import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums

namespace Formalism.IrreducibleCountingLemmas.WindowSums

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem padicValIntShiftLe : DigitLemma := by
  intro l a c ρ m hl ha hc0 hcN hρ hdvd hm
  have := Fact.mk hl
  have hl2 : (2:ℤ) ≤ (l:ℤ) := by exact_mod_cast hl.two_le
  have hla : 1 ≤ l ^ a := Nat.one_le_pow _ _ hl.pos
  have hlr : 1 ≤ l ^ ρ := Nat.one_le_pow _ _ hl.pos
  have hNc : ((l ^ a - 1 : ℕ) : ℤ) = (l:ℤ) ^ a - 1 := by
    rw [Nat.cast_sub hla]; push_cast; rfl
  have hcN' : (c:ℤ) < (l:ℤ) ^ a - 1 := by rw [← hNc]; exact_mod_cast hcN
  have hc0' : (0:ℤ) < c := by exact_mod_cast hc0
  have hdvd' : ((l:ℤ) ^ a - 1) ∣ (c:ℤ) * ((l:ℤ) ^ ρ - 1) := by
    have h1 := Int.natCast_dvd_natCast.mpr hdvd
    rw [hNc] at h1
    have h2 : ((c * (l ^ ρ - 1) : ℕ) : ℤ) = (c:ℤ) * ((l:ℤ) ^ ρ - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hlr]; push_cast; rfl
    rw [h2] at h1; exact h1
  have hP : (2:ℤ) ≤ (l:ℤ) ^ ρ := by
    obtain ⟨r, rfl⟩ : ∃ r, ρ = r + 1 := ⟨ρ - 1, by omega⟩
    have : (1:ℤ) ≤ (l:ℤ) ^ r := one_le_pow₀ (by linarith)
    rw [pow_succ]; nlinarith
  by_contra hv
  push Not at hv
  have hdx : (l:ℤ) ^ (ρ + 1) ∣ (c:ℤ) + m * ((l:ℤ) ^ a - 1) :=
    (padicValInt_dvd_iff (ρ + 1) _).2 (Or.inr (by omega))
  obtain ⟨t, ht⟩ := hdx
  have hxN : ((l:ℤ) ^ a - 1) ∣ (l:ℤ) ^ (ρ + 1) * (t * ((l:ℤ) ^ ρ - 1)) := by
    have e : (l:ℤ) ^ (ρ + 1) * (t * ((l:ℤ) ^ ρ - 1))
        = (c:ℤ) * ((l:ℤ) ^ ρ - 1) + ((l:ℤ) ^ a - 1) * (m * ((l:ℤ) ^ ρ - 1)) := by
      rw [← mul_assoc, ← ht]; ring
    rw [e]; exact dvd_add hdvd' (dvd_mul_right _ _)
  have hcop : IsCoprime ((l:ℤ) ^ a - 1) ((l:ℤ) ^ (ρ + 1)) := by
    apply IsCoprime.pow_right
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    exact ⟨-1, (l:ℤ) ^ b, by ring⟩
  have hy : ((l:ℤ) ^ a - 1) ∣ t * ((l:ℤ) ^ ρ - 1) := by
    exact hcop.dvd_of_dvd_mul_left hxN
  have hm' := abs_lt.mp hm
  have hNpos : (0:ℤ) < (l:ℤ) ^ a - 1 := by linarith
  have hxlt : |(c:ℤ) + m * ((l:ℤ) ^ a - 1)| < (l:ℤ) * ((l:ℤ) ^ a - 1) := by
    have u1 : 0 ≤ ((l:ℤ) - 1 - m) * ((l:ℤ) ^ a - 1) :=
      mul_nonneg (by linarith) hNpos.le
    have u2 : 0 ≤ (m + (l:ℤ) - 1) * ((l:ℤ) ^ a - 1) :=
      mul_nonneg (by linarith) hNpos.le
    rw [abs_lt]; constructor <;> nlinarith
  have htlt : (l:ℤ) ^ ρ * |t| < (l:ℤ) ^ a - 1 := by
    rw [ht, abs_mul, abs_of_pos (by positivity : (0:ℤ) < (l:ℤ) ^ (ρ + 1)), pow_succ] at hxlt
    have hl0 : (0:ℤ) < l := by linarith
    nlinarith
  have hylt : |t * ((l:ℤ) ^ ρ - 1)| < (l:ℤ) ^ a - 1 := by
    rw [abs_mul, abs_of_pos (by linarith : (0:ℤ) < (l:ℤ) ^ ρ - 1)]
    nlinarith [abs_nonneg t]
  have hy0 := Int.eq_zero_of_abs_lt_dvd hy hylt
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp hy0 with h | h
    · exact h
    · linarith
  rw [ht0, mul_zero] at ht
  have hcd : ((l:ℤ) ^ a - 1) ∣ (c:ℤ) := ⟨-m, by linarith⟩
  have hcz := Int.eq_zero_of_abs_lt_dvd hcd (by rw [abs_of_pos hc0']; exact hcN')
  linarith

end Formalism.IrreducibleCountingLemmas.WindowSums
