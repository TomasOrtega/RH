import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums

namespace Formalism.IrreducibleCountingLemmas.WindowSums

/- English proof (translation)
Introduce `l a c ρ m hl ha hc0 hcN hρ hdvd hm`. Use `Fact.mk hl` as an intermediate fact. Establish `hl2 : (2:ℤ) ≤ (l:ℤ)` using `by exact_mod_cast hl.two_le`. Establish `hla : 1 ≤ l ^ a` using `Nat.one_le_pow _ _ hl.pos`. Establish `hlr : 1 ≤ l ^ ρ` using `Nat.one_le_pow _ _ hl.pos`.

Establish `hNc : ((l ^ a - 1 : ℕ) : ℤ) = (l:ℤ) ^ a - 1`. Rewrite using `[Nat.cast_sub hla]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hcN' : (c:ℤ) < (l:ℤ) ^ a - 1` using `by rw [← hNc]; exact_mod_cast hcN`.

Establish `hc0' : (0:ℤ) < c` using `by exact_mod_cast hc0`. Establish `hdvd' : ((l:ℤ) ^ a - 1) ∣ (c:ℤ) * ((l:ℤ) ^ ρ - 1)`. Establish `h1` using `Int.natCast_dvd_natCast.mpr hdvd`. Rewrite `h1` using `[hNc]`. Establish `h2 : ((c * (l ^ ρ - 1) : ℕ) : ℤ) = (c:ℤ) * ((l:ℤ) ^ ρ - 1)`.

Rewrite using `[Nat.cast_mul, Nat.cast_sub hlr]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `h1` using `[h2]`. Conclude with `h1`.

Establish `hP : (2:ℤ) ≤ (l:ℤ) ^ ρ`. Take `⟨r, rfl⟩ : ∃ r, ρ = r + 1` from `⟨ρ - 1, by omega⟩`. Establish `: (1:ℤ) ≤ (l:ℤ) ^ r` using `one_le_pow₀ (by linarith)`. Rewrite using `[pow_succ]`. Use the polynomial consequences of the given equalities and inequalities.

Assume the negation of the conclusion as `hv`. Use `push Not at hv`. Establish `hdx : (l:ℤ) ^ (ρ + 1) ∣ (c:ℤ) + m * ((l:ℤ) ^ a - 1)` using `(padicValInt_dvd_iff (ρ + 1) _).2 (Or.inr (by omega))`. Take `⟨t, ht⟩` from `hdx`. Establish `hxN : ((l:ℤ) ^ a - 1) ∣ (l:ℤ) ^ (ρ + 1) * (t * ((l:ℤ) ^ ρ - 1))`.

Establish `e : (l:ℤ) ^ (ρ + 1) * (t * ((l:ℤ) ^ ρ - 1)) = (c:ℤ) * ((l:ℤ) ^ ρ - 1) + ((l:ℤ) ^ a - 1) * (m * ((l:ℤ) ^ ρ - 1))`. Rewrite using `[← mul_assoc, ← ht]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add hdvd' (dvd_mul_right _ _)`.

Establish `hcop : IsCoprime ((l:ℤ) ^ a - 1) ((l:ℤ) ^ (ρ + 1))`. Apply `IsCoprime.pow_right` to reduce the goal to its premises. Take `⟨b, rfl⟩ : ∃ b, a = b + 1` from `⟨a - 1, by omega⟩`. Conclude with `⟨-1, (l:ℤ) ^ b, by ring⟩`. Establish `hy : ((l:ℤ) ^ a - 1) ∣ t * ((l:ℤ) ^ ρ - 1)`.

Conclude with `hcop.dvd_of_dvd_mul_left hxN`. Establish `hm'` using `abs_lt.mp hm`. Establish `hNpos : (0:ℤ) < (l:ℤ) ^ a - 1` using `by linarith`. Establish `hxlt : |(c:ℤ) + m * ((l:ℤ) ^ a - 1)| < (l:ℤ) * ((l:ℤ) ^ a - 1)`. Establish `u1 : 0 ≤ ((l:ℤ) - 1 - m) * ((l:ℤ) ^ a - 1)` using `mul_nonneg (by linarith) hNpos.le`.

Establish `u2 : 0 ≤ (m + (l:ℤ) - 1) * ((l:ℤ) ^ a - 1)` using `mul_nonneg (by linarith) hNpos.le`. Apply the tactic sequence `rw [abs_lt]; constructor <;> nlinarith`. Establish `htlt : (l:ℤ) ^ ρ * |t| < (l:ℤ) ^ a - 1`. Rewrite `hxlt` using `[ht, abs_mul, abs_of_pos (by positivity : (0:ℤ) < (l:ℤ) ^ (ρ + 1)), pow_succ]`. Establish `hl0 : (0:ℤ) < l` using `by linarith`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hylt : |t * ((l:ℤ) ^ ρ - 1)| < (l:ℤ) ^ a - 1`. Rewrite using `[abs_mul, abs_of_pos (by linarith : (0:ℤ) < (l:ℤ) ^ ρ - 1)]`. Use polynomial arithmetic with `[abs_nonneg t]`. Establish `hy0` using `Int.eq_zero_of_abs_lt_dvd hy hylt`.

Establish `ht0 : t = 0`. Break down `mul_eq_zero.mp hy0 with h | h` into its components or cases. Conclude with `h`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `ht` using `[ht0, mul_zero]`.

Establish `hcd : ((l:ℤ) ^ a - 1) ∣ (c:ℤ)` using `⟨-m, by linarith⟩`. Establish `hcz` using `Int.eq_zero_of_abs_lt_dvd hcd (by rw [abs_of_pos hc0']; exact hcN')`. Combine the linear equalities and inequalities to obtain the conclusion.
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
