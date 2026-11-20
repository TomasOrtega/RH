import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.FunctionalEquationGL2GL1Complex
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchwartzSlice

open Ad3.K.LC Ad3.K.LC.C

noncomputable def sliceMap (X : M23) : (Fin 2 → ℂ) → M23 × (Fin 2 → ℂ) := fun q => (X, q)

/- English proof (translation)
Establish `h : sliceMap X = fun q => (X, (0 : Fin 2 → ℂ)) + (ContinuousLinearMap.inr ℝ M23 (Fin 2 → ℂ)) q`. Use function extensionality and compare the values at `q`. Simplify using `[sliceMap]`. Rewrite using `[h]`. Conclude with `(Function.HasTemperateGrowth.const _).add (ContinuousLinearMap.inr ℝ M23 (Fin 2 → ℂ)).hasTemperateGrowth`.
-/
theorem sliceMap_temperate (X : M23) : (sliceMap X).HasTemperateGrowth := by
  have h : sliceMap X = fun q => (X, (0 : Fin 2 → ℂ)) + (ContinuousLinearMap.inr ℝ M23 (Fin 2 → ℂ)) q := by
    funext q
    simp [sliceMap]
  rw [h]
  exact (Function.HasTemperateGrowth.const _).add (ContinuousLinearMap.inr ℝ M23 (Fin 2 → ℂ)).hasTemperateGrowth

/- English proof (translation)
Use `⟨1, 1, fun q => ?_⟩` and prove the remaining obligations. Establish `h : ‖q‖ ≤ ‖sliceMap X q‖`. Simplify using `only [sliceMap, Prod.norm_def]`. Conclude with `le_max_right _ _`. Simplify using `only [pow_one, one_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sliceMap_upper (X : M23) :
    ∃ (k : ℕ) (C : ℝ), ∀ q, ‖q‖ ≤ C * (1 + ‖sliceMap X q‖) ^ k := by
  refine ⟨1, 1, fun q => ?_⟩
  have h : ‖q‖ ≤ ‖sliceMap X q‖ := by
    simp only [sliceMap, Prod.norm_def]
    exact le_max_right _ _
  simp only [pow_one, one_mul]
  linarith

/- English proof (translation)
Introduce `Ψ X`. Use `⟨SchwartzMap.compCLM ℂ (sliceMap_temperate X) (sliceMap_upper X) Ψ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Both sides reduce to the same expression.
-/
theorem slices_schwartz : Ad3.K.LC.C.SlS := by
  intro Ψ X
  refine ⟨SchwartzMap.compCLM ℂ (sliceMap_temperate X) (sliceMap_upper X) Ψ, ?_⟩
  funext q
  rfl

end GlobalTheory.CompanionTheory.SchwartzSlice
