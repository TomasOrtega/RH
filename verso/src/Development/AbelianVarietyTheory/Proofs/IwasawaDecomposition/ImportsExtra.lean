import Mathlib

namespace GlobalTheory.IsolatedTheoremFive

/- English proof (translation)
Establish `hl : LinearMap.ker (Matrix.mulVecLin E) = ⊥` using `LinearMap.ker_eq_bot.mpr h`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin E) hl`. Establish `hB : LinearMap.toMatrix' g * E = 1`. Establish `e : Matrix.mulVecLin E = Matrix.toLin' E` using `rfl`. Establish `: LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin E) = LinearMap.toMatrix' g * E`.

Rewrite using `[LinearMap.toMatrix'_comp, e, LinearMap.toMatrix'_toLin']`. Rewrite using `[← this, hg, LinearMap.toMatrix'_id]`. Establish `hB' : (LinearMap.toMatrix' g).map φ * E.map φ = 1`. Rewrite using `[← Matrix.map_mul, hB, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Introduce `x y hxy`.

Use `congrArg (Matrix.mulVec ((LinearMap.toMatrix' g).map φ)) hxy` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hB']`.
-/
theorem main {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n d : ℕ}
    (E : Matrix (Fin n) (Fin d) K) (h : Function.Injective (Matrix.mulVec E)) :
    Function.Injective (Matrix.mulVec (Matrix.map E (⇑φ : K → K'))) := by
  have hl : LinearMap.ker (Matrix.mulVecLin E) = ⊥ := LinearMap.ker_eq_bot.mpr h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin E) hl
  have hB : LinearMap.toMatrix' g * E = 1 := by
    have e : Matrix.mulVecLin E = Matrix.toLin' E := rfl
    have : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin E) = LinearMap.toMatrix' g * E := by
      rw [LinearMap.toMatrix'_comp, e, LinearMap.toMatrix'_toLin']
    rw [← this, hg, LinearMap.toMatrix'_id]
  have hB' : (LinearMap.toMatrix' g).map φ * E.map φ = 1 := by
    rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero φ) (map_one φ)]
  intro x y hxy
  have := congrArg (Matrix.mulVec ((LinearMap.toMatrix' g).map φ)) hxy
  simpa [Matrix.mulVec_mulVec, hB'] using this

/- English proof (translation)
Introduce `K K' _ _ φ n d E h`. Conclude with `main φ E h`.
-/
theorem target : ∀ {K K' : Type} [inst : Field K] [inst_1 : Field K'] (φ : K →+* K') {n d : ℕ} (E : Matrix (Fin n) (Fin d) K), Function.Injective (Matrix.mulVec E) → Function.Injective (Matrix.mulVec (Matrix.map E (⇑φ : K → K'))) := by
  intro K K' _ _ φ n d E h
  exact main φ E h

end GlobalTheory.IsolatedTheoremFive
