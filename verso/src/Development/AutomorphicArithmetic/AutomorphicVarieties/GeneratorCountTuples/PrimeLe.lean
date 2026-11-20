import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge

open NumberField UpperTheory.V UpperTheory.V.K

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.K.primeLe :
    ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L], HasMuQ l L → l ≤ Module.finrank ℚ L + 1 := by
  intro l hl L _ _ hL
  obtain ⟨ζ, hζ⟩ := hL
  have hp := hl.out
  by_cases h2 : l = 2
  · subst h2
    have := Module.finrank_pos (R := ℚ) (M := L)
    omega
  · rw [if_neg h2] at hζ
    have hdeg := minpoly.natDegree_le (A := ℚ) ζ
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ hp.pos, Polynomial.natDegree_cyclotomic,
      Nat.totient_prime hp] at hdeg
    omega
