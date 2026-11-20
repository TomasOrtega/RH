import Mathlib
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.AltSpan

/- English proof (translation)
Introduce `P _ _ M _ _ β b hb m f hf`. Establish `key : ∀ (S : Finset (Fin m)) (v : Fin m → P), (∀ i ∉ S, v i ∈ Set.range b) → f v = 0`. Introduce `S`. Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Introduce `v hv choose I hI using fun i => hv i (by simp)`.

Establish `hvI : v = b ∘ I` using `funext fun i => (hI i).symm`. Rewrite using `[hvI]`. Conclude with `hf I`. Introduce `j S _ ih v hv`. Establish `hlin : f.toMultilinearMap.toLinearMap v j = 0`.

Apply `LinearMap.ext_on_range hb` to reduce the goal to its premises. Introduce `c`. Simplify using `only [MultilinearMap.toLinearMap_apply, LinearMap.zero_apply, AlternatingMap.coe_multilinearMap]`. Apply `ih` to reduce the goal to its premises. Introduce `i hi`.

Distinguish the cases in `hij : i = j`. Rewrite using `[hij]`. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hij]`. Conclude with `hv i (by simp [hij, hi])`.

Establish `h1` using `LinearMap.congr_fun hlin (v j)`. Simplify `h1` using `[MultilinearMap.toLinearMap_apply]`. Use extensionality with `v`. Simplify using `using key Finset.univ v (by simp)`.
-/
theorem alternatingMap_eq_zero_of_span :
    ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℝ M]
      {β : Type} (b : β → P), Submodule.span ℝ (Set.range b) = ⊤ →
      ∀ {m : ℕ} (f : P [⋀^Fin m]→ₗ[ℝ] M), (∀ I : Fin m → β, f (b ∘ I) = 0) → f = 0 := by
  intro P _ _ M _ _ β b hb m f hf
  classical
  have key : ∀ (S : Finset (Fin m)) (v : Fin m → P), (∀ i ∉ S, v i ∈ Set.range b) → f v = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro v hv
      choose I hI using fun i => hv i (by simp)
      have hvI : v = b ∘ I := funext fun i => (hI i).symm
      rw [hvI]
      exact hf I
    · intro j S _ ih v hv
      have hlin : f.toMultilinearMap.toLinearMap v j = 0 := by
        apply LinearMap.ext_on_range hb
        intro c
        simp only [MultilinearMap.toLinearMap_apply, LinearMap.zero_apply, AlternatingMap.coe_multilinearMap]
        apply ih
        intro i hi
        by_cases hij : i = j
        · rw [hij]
          simp
        · rw [Function.update_of_ne hij]
          exact hv i (by simp [hij, hi])
      have h1 := LinearMap.congr_fun hlin (v j)
      simpa [MultilinearMap.toLinearMap_apply] using h1
  ext v
  simpa using key Finset.univ v (by simp)

end GlobalTheory.CompanionTheory.AltSpan
