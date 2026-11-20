import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.LevelFamily
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Introduce `Λ la hla θ hθ0 hθ1 hW`. Take `⟨F, hG, hZ⟩` from `UpperTheory.Comparison₂.level_family Λ`. Rewrite using `[← hZ]`. Use `Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith) fun Y₀ => ?_` and prove the remaining obligations. Take `⟨Y, hY, hx⟩` from `hW Y₀`.

Use `⟨Y, hY, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : ℝ) + (la - 1) = la` using `by ring`. Rewrite `hy` using `[h1]`. Rewrite using `[hG, one_mul]`. Conclude with `hx y hy.1 hy.2`.
-/
theorem UpperTheory.Comparison₂.formB :
    ∀ Λ : Level, Λ.FormB := by
  intro Λ la hla θ hθ0 hθ1 hW
  obtain ⟨F, hG, hZ⟩ := UpperTheory.Comparison₂.level_family Λ
  rw [← hZ]
  refine Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith) fun Y₀ => ?_
  obtain ⟨Y, hY, hx⟩ := hW Y₀
  refine ⟨Y, hY, fun y hy => ?_⟩
  have h1 : (1 : ℝ) + (la - 1) = la := by ring
  rw [h1] at hy
  rw [hG, one_mul]
  exact hx y hy.1 hy.2
