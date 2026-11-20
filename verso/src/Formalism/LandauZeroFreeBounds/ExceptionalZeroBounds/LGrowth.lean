import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
import Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum

open Complex Finset

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hbij : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q))`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨fun a b hab => Fin.ext ?_, by simp [ZMod.card]⟩` and prove the remaining obligations. Establish `h1` using `congrArg ZMod.val hab`. Simplify `h1` using `[ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt]`.

Rewrite using `[Finset.sum_range, Fintype.sum_bijective _ hbij (fun i => χ ((i : ℕ) : ZMod q)) χ (fun _ => rfl)]`. Conclude with `MulChar.sum_eq_zero_of_ne_one hχ`.
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

/- English proof (translation)
Rewrite using `[Finset.sum_range_add, character_sum_range_modulus_eq_zero χ hχ, zero_add]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_add, ZMod.natCast_self, zero_add]`.
-/
lemma character_sum_range_add_modulus {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ range (q + M), χ (n : ZMod q) = ∑ n ∈ range M, χ (n : ZMod q) := by
  rw [Finset.sum_range_add, character_sum_range_modulus_eq_zero χ hχ, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Nat.cast_add, ZMod.natCast_self, zero_add]

/- English proof (translation)
Proceed by induction on `M using Nat.strong_induction_on with`. Consider the case `_ M ih`. Distinguish the cases in `hM : M < q`. Combine the equalities or inequalities in the displayed calculation. Take `⟨M', rfl⟩ : ∃ M', M = q + M'` from `⟨M - q, by omega⟩`.

Rewrite using `[character_sum_range_add_modulus χ hχ M']`. Conclude with `ih M' (by have := NeZero.pos q; omega)`.
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

/- English proof (translation)
Establish `h1 : ∑ n ∈ range (M + 1), χ (n : ZMod q) = χ ((0 : ℕ) : ZMod q) + ∑ n ∈ Icc 1 M, χ (n : ZMod q)`. Establish `hI : Finset.Ico 1 (M + 1) = Finset.Icc 1 M`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ico, Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M), zero_add, hI]`. Establish `h2 : ∑ n ∈ Icc 1 M, χ (n : ZMod q) = ∑ n ∈ range (M + 1), χ (n : ZMod q) - χ ((0 : ℕ) : ZMod q)`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Combine the equalities or inequalities in the displayed calculation.
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

/- English proof (translation)
Use `⟨9, ?_⟩` and prove the remaining obligations. Introduce `q _ χ hχ s hs`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast NeZero.one_le`. Establish `hσ : 0 < s.re` using `by linarith`. Establish `hB` using `norm_character_sum_Icc_le χ hχ`.

Establish `hP` using `Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) hB s hσ 1 le_rfl`. Simplify using `only [Nat.cast_one, Real.one_rpow, mul_one, Finset.Icc_self, Finset.sum_singleton] at hP`. Establish `h1 : ‖χ (1 : ZMod q) * (1 : ℂ) ^ (-s)‖ ≤ 1`. Rewrite using `[one_cpow, mul_one]`. Conclude with `DirichletCharacter.norm_le_one χ _`.

Establish `hs0 : 0 ≤ ‖s‖` using `norm_nonneg s`. Establish `hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖`. Rewrite using `[div_le_iff₀ hσ]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hL : ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re)`.

Use `norm_le_insert' (DirichletCharacter.LFunction χ s) (χ (1 : ZMod q) * (1 : ℂ) ^ (-s))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
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
