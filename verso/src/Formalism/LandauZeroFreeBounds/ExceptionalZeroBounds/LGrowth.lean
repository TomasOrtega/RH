import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
import Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum

open Complex Finset

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
The integers from zero through q − 1 map bijectively to the residues modulo q. Reindex the sum by those residues and use the vanishing of the full sum of a nonprincipal character.
-/
lemma character_sum_range_modulus_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  have hbij : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => Fin.ext ?_, by simp [ZMod.card]⟩
    have h1 := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h1
  rw [Finset.sum_range, Fintype.sum_bijective _ hbij (fun i => χ ((i : ℕ) : ZMod q)) χ (fun _ => rfl)]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/- English proof (authored)
Split the range after the first q terms. The first block is a complete period and sums to zero. In the second block adding q does not change a residue, so its sum is exactly the original range sum of length M.
-/
lemma character_sum_range_add_modulus {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ range (q + M), χ (n : ZMod q) = ∑ n ∈ range M, χ (n : ZMod q) := by
  rw [Finset.sum_range_add, character_sum_range_modulus_eq_zero χ hχ, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Nat.cast_add, ZMod.natCast_self, zero_add]

/- English proof (authored)
Use induction on M. Below q the triangle inequality and the bound of one on the character values give a bound of M, hence q. At or above q remove one complete period, whose sum vanishes. The remaining range is strictly shorter and satisfies the bound by induction.
-/
lemma norm_character_sum_range_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ q := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases hM : M < q
    · calc ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ ∑ n ∈ range M, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ range M, (1 : ℝ) := Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
        _ = M := by simp
        _ ≤ q := by exact_mod_cast hM.le
    · obtain ⟨M', rfl⟩ : ∃ M', M = q + M' := ⟨M - q, by omega⟩
      rw [character_sum_range_add_modulus χ hχ M']
      exact ih M' (by have := NeZero.pos q; omega)

/- English proof (authored)
The sum from one to M is the range sum of length M + 1 with its term at zero subtracted. The range sum has norm at most q and the removed term has norm at most one. Apply the triangle inequality.
-/
lemma norm_character_sum_Icc_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Icc 1 M, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have h1 : ∑ n ∈ range (M + 1), χ (n : ZMod q) =
      χ ((0 : ℕ) : ZMod q) + ∑ n ∈ Icc 1 M, χ (n : ZMod q) := by
    have hI : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M), zero_add, hI]
  have h2 : ∑ n ∈ Icc 1 M, χ (n : ZMod q) =
      ∑ n ∈ range (M + 1), χ (n : ZMod q) - χ ((0 : ℕ) : ZMod q) := by
    rw [h1]; ring
  rw [h2]
  calc _ ≤ ‖∑ n ∈ range (M + 1), χ (n : ZMod q)‖ + ‖χ ((0 : ℕ) : ZMod q)‖ := norm_sub_le _ _
    _ ≤ q + 1 := add_le_add (norm_character_sum_range_le χ hχ _) (DirichletCharacter.norm_le_one χ _)

/- English proof (authored)
Apply the partial-sum L-function estimate with character-sum bound q + 1 and cutoff one. The single retained term has norm at most one. The error is bounded by 2(q + 1)(1 + |s|/Re(s)). Since the real part is at least one half, that ratio is at most twice the norm. Use q ≥ 1 to simplify the result to the stated linear bound.
-/
theorem lfunction_polynomial_growth : LGrowth := by
  refine ⟨9, ?_⟩
  intro q _ χ hχ s hs
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hσ : 0 < s.re := by linarith
  have hB := norm_character_sum_Icc_le χ hχ
  have hP := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) hB s hσ 1 le_rfl
  simp only [Nat.cast_one, Real.one_rpow, mul_one, Finset.Icc_self, Finset.sum_singleton] at hP
  have h1 : ‖χ (1 : ZMod q) * (1 : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [one_cpow, mul_one]; exact DirichletCharacter.norm_le_one χ _
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    rw [div_le_iff₀ hσ]; nlinarith
  have hL : ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := by
    have := norm_le_insert' (DirichletCharacter.LFunction χ s) (χ (1 : ZMod q) * (1 : ℂ) ^ (-s))
    linarith
  calc ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := hL
    _ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + 2 * ‖s‖) := by gcongr
    _ ≤ 9 * q * (1 + ‖s‖) := by nlinarith

end Formalism.ZeroFreeDirichlet
