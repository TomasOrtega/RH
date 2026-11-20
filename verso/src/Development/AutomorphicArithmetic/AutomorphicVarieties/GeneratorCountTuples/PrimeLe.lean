import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge

open NumberField UpperTheory.V UpperTheory.V.K

/- English proof (translation)
Introduce `l hl L _ _ hL`. Take `⟨ζ, hζ⟩` from `hL`. Establish `hp` using `hl.out`. Distinguish the cases in `h2 : l = 2`. Substitute `h2` using the available equality.

Use `Module.finrank_pos (R := ℚ) (M := L)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `hζ` using `[if_neg h2]`. Establish `hdeg` using `minpoly.natDegree_le (A := ℚ) ζ`. Rewrite `hdeg` using `[← Polynomial.cyclotomic_eq_minpoly_rat hζ hp.pos, Polynomial.natDegree_cyclotomic, Nat.totient_prime hp]`.

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
