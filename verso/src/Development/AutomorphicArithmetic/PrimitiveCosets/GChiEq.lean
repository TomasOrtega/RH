import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.Comparison₂.gChi_eq_ramp (f : ℕ → ℂ) (y : ℝ) :
    Deduction.ramp f y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (An.abelian₂ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
  unfold Deduction.ramp
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), zero_add]
  have e : Finset.Ico 1 ⌊y⌋₊.succ = Finset.Icc 1 ⌊y⌋₊ := by
    ext n
    simp [Nat.lt_succ_iff]
  rw [e]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.Comparison₂.gChi_eq :
    ∀ (ψ : PChar) (y : ℝ), An.gChi ψ.χ y = Deduction.Gchi ψ.χ y := by
  intro ψ y
  unfold An.gChi Deduction.Gchi
  rw [UpperTheory.Comparison₂.gChi_eq_ramp]
  by_cases h : ψ.χ = 1
  · rw [if_pos h, if_pos h]
    have hN : ψ.N = 1 := by
      have hp : ψ.χ.conductor = ψ.N := ψ.prim
      rw [h, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    have h2 : ∀ n : ℕ, ψ.χ (n : ZMod ψ.N) = 1 := fun n => by
      rw [h]
      refine MulChar.one_apply ?_
      rw [ZMod.isUnit_iff_coprime, hN]
      exact Nat.coprime_one_right n
    simp only [h2, An.G, mul_one]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    rfl
