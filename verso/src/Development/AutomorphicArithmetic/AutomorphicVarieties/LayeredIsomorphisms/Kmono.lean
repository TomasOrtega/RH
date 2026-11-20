import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Introduce `C C' hCC hK`. Unfold `LemmaK at hK ⊢`. Introduce `l _ L Ω _ _ _ _ _ D hL hMu e he`. Take `⟨hf, hb⟩` from `hK l L Ω D hL hMu e he`. Use `⟨hf, hb.trans ?_⟩` and prove the remaining obligations.

Unfold `kBound`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_right` to reduce the goal to its premises. Apply `Real.rpow_le_rpow_of_exponent_le _ hCC` to reduce the goal to its premises. Establish `hn : 0 < Module.finrank ℚ L` using `Module.finrank_pos`.

Establish `h1 : (1 : ℝ) ≤ (e : ℝ)` using `by exact_mod_cast he`. Establish `h2 : (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ)` using `by exact_mod_cast hn`. Use the polynomial consequences of the given equalities and inequalities. Break down `Nat.eq_zero_or_pos (discr L).natAbs with h0 | h0` into its components or cases. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `: (1 : ℝ) ≤ ((discr L).natAbs : ℝ)` using `by exact_mod_cast h0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Win.kmono :
    ∀ C C' : ℝ, C ≤ C' → LemmaK C → LemmaK C' := by
  intro C C' hCC hK
  unfold LemmaK at hK ⊢
  intro l _ L Ω _ _ _ _ _ D hL hMu e he
  obtain ⟨hf, hb⟩ := hK l L Ω D hL hMu e he
  refine ⟨hf, hb.trans ?_⟩
  unfold kBound
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right
  · apply Real.rpow_le_rpow_of_exponent_le _ hCC
    have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
    have h1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have h2 : (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) := by exact_mod_cast hn
    nlinarith
  · rcases Nat.eq_zero_or_pos (discr L).natAbs with h0 | h0
    · rw [h0]
      simp
    · apply Real.log_nonneg
      have : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := by exact_mod_cast h0
      linarith
