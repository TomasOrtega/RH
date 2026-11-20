import Mathlib

open MvPolynomial Filter Topology

/- English proof (translation)
Introduce `σ B _ x y h`. Establish `h1 : ∀ s, ∃ i, y s i ≠ x i` using `fun s => Function.ne_iff.mp (h s)`. Use `choose i hi using h1`. Use `⟨∏ s, C (x (i s) - y s (i s))⁻¹ * (X (i s) - C (y s (i s))), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`.

Use `Finset.prod_eq_one fun s _ => ?_` and prove the remaining obligations. Establish `hne : x (i s) - y s (i s) ≠ 0` using `sub_ne_zero.mpr (hi s).symm`. Rewrite using `[map_mul, map_sub, eval_C, eval_C, eval_X, inv_mul_cancel₀ hne]`. Introduce `s`. Rewrite using `[map_prod]`.

Use `Finset.prod_eq_zero (Finset.mem_univ s) ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_sub, eval_C, eval_C, eval_X, sub_self, mul_zero]`.
-/
theorem UpperTheory.ConvolutionTheory.FX.separate_points :
    ∀ (σ B : Type) [Fintype B] (x : σ → ℂ) (y : B → σ → ℂ), (∀ s, y s ≠ x) → ∃ p : MvPolynomial σ ℂ, eval x p = 1 ∧ ∀ s, eval (y s) p = 0 := by
  intro σ B _ x y h
  classical
  have h1 : ∀ s, ∃ i, y s i ≠ x i := fun s => Function.ne_iff.mp (h s)
  choose i hi using h1
  refine ⟨∏ s, C (x (i s) - y s (i s))⁻¹ * (X (i s) - C (y s (i s))), ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_eq_one fun s _ => ?_
    have hne : x (i s) - y s (i s) ≠ 0 := sub_ne_zero.mpr (hi s).symm
    rw [map_mul, map_sub, eval_C, eval_C, eval_X, inv_mul_cancel₀ hne]
  · intro s
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    rw [map_mul, map_sub, eval_C, eval_C, eval_X, sub_self, mul_zero]
