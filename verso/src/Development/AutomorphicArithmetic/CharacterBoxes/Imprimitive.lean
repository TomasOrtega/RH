import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

open Formalism.HC

/- English proof (translation)
Introduce `h N _ χ s hs hχs`. Use `haveI : NeZero χ.conductor := (PChar.of χ).ne`. Establish `hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0` using `h (PChar.of χ) trivial s hs`. Establish `hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1`. Break down `hχs with hχ | hs1` into its components or cases.

Use `left`. Introduce `h1`. Apply `hχ` to reduce the goal to its premises. Rewrite using `[← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]`. Conclude with `Or.inr hs1`.

Establish `hrw` using `DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'`. Rewrite `hrw` using `[χ.changeLevel_primitiveCharacter]`. Rewrite using `[hrw]`. Use `mul_ne_zero hL (Finset.prod_ne_zero_iff.mpr fun p hp => ?_)` and prove the remaining obligations. Establish `hp'` using `Nat.prime_of_mem_primeFactors hp`.

Introduce `h0`. Establish `key : χ.primitiveCharacter p * (p : ℂ) ^ (-s) = 1` using `by linear_combination -h0`. Establish `h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1` using `DirichletCharacter.norm_le_one _ _`. Establish `h2 : ‖(p : ℂ) ^ (-s)‖ < 1`. Rewrite using `[Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]`.

Conclude with `Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)`. Establish `hn : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hn` using `[key, norm_one]`.

Conclude with `lt_irrefl _ hn`.
-/
theorem UpperTheory.Top.imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h N _ χ s hs hχs
  haveI : NeZero χ.conductor := (PChar.of χ).ne
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
  have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with hχ | hs1
    · left
      intro h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    · exact Or.inr hs1
  have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
  rw [χ.changeLevel_primitiveCharacter] at hrw
  rw [hrw]
  refine mul_ne_zero hL (Finset.prod_ne_zero_iff.mpr fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  intro h0
  have key : χ.primitiveCharacter p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h0
  have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
  have hn : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-s)‖
        ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by gcongr
      _ < 1 := by simpa using h2
  rw [key, norm_one] at hn
  exact lt_irrefl _ hn
