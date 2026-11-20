import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeightBlockEmbeddingLe

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce `K _ _ a n e Γ S`. Prove the components needed by the constructor for the conclusion. Introduce `hG φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem f hf`.

Take `⟨ψ, hψ, g, -, hfm⟩` from `hf`. Take `⟨C, N, hC⟩` from `hG ψ hψ`. Establish `hC0 : 0 ≤ C`. Establish `h1` using `(norm_nonneg _).trans (hC 1)`. Establish `hp : 0 < height (1 : AdelicGLn.AdelicGL K n) ^ N` using `pow_pos (height_pos _) N`.

Conclude with `le_of_mul_le_mul_right (by rw [zero_mul]; exact h1) hp`. Establish `hc : 0 ≤ heightConst K n * height g` using `mul_nonneg (zero_le_one.trans (one_le_heightConst (K := K) (n := n))) (height_pos g).le`. Use `⟨C * (heightConst K n * height g) ^ N, N, fun m => ?_⟩` and prove the remaining obligations. Establish `hh : height (g * emb e m) ≤ heightConst K n * height g * height m` using `(height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (UpperTheory.height_blockEmbedding_le K a n e m) hc)`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `zero => simpa using (hasModerateGrowth_zero (K := K) (n := a))`. Consider the case `add x y _ _ hx hy => simpa using hx.add hy`. Consider the case `smul c x _ hx => simpa using hx.smul c`. Introduce and unpack `⟨L, hL, hinv⟩`. Set `f : AdelicGLn.FiniteAdelicGL K a →* AdelicGLn.FiniteAdelicGL K n` to `emb e`.

Use `⟨L.comap f, hL.preimage (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).2.2, fun φ hφ => ?_⟩` and prove the remaining obligations. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem h hh`. Take `⟨ψ, hψ, g, -, hfm⟩` from `hh`. Introduce `u hu m`.

Rewrite using `[hfm, hfm, map_mul, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).1 u, ← mul_assoc]`. Conclude with `hinv ψ hψ (f u) hu _`. Consider the case `zero => intro u _ m`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro u hu m`.

Simplify using `[hx u hu m, hy u hu m]`. Consider the case `smul c x _ hx => intro u hu m`. Simplify using `[hx u hu m]`.
-/
theorem UpperTheory.slSp_preserves_growth_and_level :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), (Growth S → Growth (slSp e Γ S)) ∧ (Level S → Level (slSp e Γ S)) := by
  intro K _ _ a n e Γ S
  constructor
  · intro hG φ hφ
    induction hφ using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hf
      obtain ⟨C, N, hC⟩ := hG ψ hψ
      have hC0 : 0 ≤ C := by
        have h1 := (norm_nonneg _).trans (hC 1)
        have hp : 0 < height (1 : AdelicGLn.AdelicGL K n) ^ N := pow_pos (height_pos _) N
        exact le_of_mul_le_mul_right (by rw [zero_mul]; exact h1) hp
      have hc : 0 ≤ heightConst K n * height g :=
        mul_nonneg (zero_le_one.trans (one_le_heightConst (K := K) (n := n))) (height_pos g).le
      refine ⟨C * (heightConst K n * height g) ^ N, N, fun m => ?_⟩
      have hh : height (g * emb e m) ≤ heightConst K n * height g * height m :=
        (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (UpperTheory.height_blockEmbedding_le K a n e m) hc)
      calc ‖(f : AdelicGLn.AdelicGL K a → ℂ) m‖ = ‖(ψ : AdelicGLn.AdelicGL K n → ℂ) (g * emb e m)‖ := by rw [hfm]
        _ ≤ C * height (g * emb e m) ^ N := hC _
        _ ≤ C * (heightConst K n * height g * height m) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le hh N) hC0
        _ = C * (heightConst K n * height g) ^ N * height m ^ N := by rw [mul_pow]; ring
    | zero => simpa using (hasModerateGrowth_zero (K := K) (n := a))
    | add x y _ _ hx hy => simpa using hx.add hy
    | smul c x _ hx => simpa using hx.smul c
  · rintro ⟨L, hL, hinv⟩
    let f : AdelicGLn.FiniteAdelicGL K a →* AdelicGLn.FiniteAdelicGL K n := emb e
    refine ⟨L.comap f, hL.preimage (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).2.2, fun φ hφ => ?_⟩
    induction hφ using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hh
      intro u hu m
      rw [hfm, hfm, map_mul, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).1 u, ← mul_assoc]
      exact hinv ψ hψ (f u) hu _
    | zero => intro u _ m; simp
    | add x y _ _ hx hy => intro u hu m; simp [hx u hu m, hy u hu m]
    | smul c x _ hx => intro u hu m; simp [hx u hu m]
