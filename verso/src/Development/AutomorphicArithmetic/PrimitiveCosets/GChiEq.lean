import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Unfold `Deduction.ramp`. Rewrite using `[Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), zero_add]`. Establish `e : Finset.Ico 1 ⌊y⌋₊.succ = Finset.Icc 1 ⌊y⌋₊`. Use extensionality with `n`. Simplify using `[Nat.lt_succ_iff]`.

Rewrite using `[e]`. Simplify using the standard rewrite rules.
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
Introduce `ψ y`. Unfold `An.gChi Deduction.Gchi`. Rewrite using `[UpperTheory.Comparison₂.gChi_eq_ramp]`. Distinguish the cases in `h : ψ.χ = 1`. Rewrite using `[if_pos h, if_pos h]`.

Establish `hN : ψ.N = 1`. Establish `hp : ψ.χ.conductor = ψ.N` using `ψ.prim`. Rewrite `hp` using `[h, DirichletCharacter.conductor_one]`. Conclude with `hp.symm`. Establish `h2 : ∀ n : ℕ, ψ.χ (n : ZMod ψ.N) = 1` using `fun n => by`.

Rewrite using `[h]`. Use `MulChar.one_apply ?_` and prove the remaining obligations. Rewrite using `[ZMod.isUnit_iff_coprime, hN]`. Conclude with `Nat.coprime_one_right n`. Simplify using `only [h2, An.G, mul_one]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg h]`. Both sides reduce to the same expression.
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
