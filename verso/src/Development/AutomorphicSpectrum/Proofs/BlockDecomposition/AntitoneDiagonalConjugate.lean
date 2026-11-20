import Mathlib
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.FrameSort

/- English proof (translation)
Introduce `n U₀ d hU`. Choose the witnesses or unpack the hypotheses as in `⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), Antitone (d ∘ σ) := by`. Use `⟨Tuple.sort (fun i => - d i), ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Use `Tuple.monotone_sort (fun i => - d i) hab` as an intermediate fact.

Simplify using `using this`. Establish `hH : (U₀.submatrix id σ)ᴴ = U₀ᴴ.submatrix σ id`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hconj : ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀.submatrix id σ)ᴴ * Z * U₀.submatrix id σ = (U₀ᴴ * Z * U₀).submatrix σ σ`.

Introduce `Z`. Rewrite using `[hH]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`. Use `⟨U₀.submatrix id σ, ?_, d ∘ σ, hσ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Establish `h1` using `hconj 1`. Rewrite `h1` using `[Matrix.mul_one]`. Rewrite using `[h1, Matrix.mul_one]`. Establish `h2 : U₀ᴴ * U₀ = 1`.

Use `Matrix.mem_unitaryGroup_iff'.mp hU` as an intermediate fact. Simplify `this` using `[Matrix.star_eq_conjTranspose]`. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Rewrite using `[hH]`.

Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.submatrix_apply, id, Function.comp]`. Conclude with `Equiv.sum_comp σ (fun i => U₀ a i * (d i : ℂ) * U₀ᴴ i b)`. Introduce `Z hZ`.

Rewrite using `[hconj Z]`. Introduce `i j hij`. Simplify using `using hZ (fun e => hij (σ.injective e))`.
-/
theorem exists_antitone_reorder : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by
  intro n U₀ d hU
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), Antitone (d ∘ σ) := by
    refine ⟨Tuple.sort (fun i => - d i), ?_⟩
    intro a b hab
    have := Tuple.monotone_sort (fun i => - d i) hab
    simpa using this
  have hH : (U₀.submatrix id σ)ᴴ = U₀ᴴ.submatrix σ id := by
    ext i j; simp
  have hconj : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      (U₀.submatrix id σ)ᴴ * Z * U₀.submatrix id σ = (U₀ᴴ * Z * U₀).submatrix σ σ := by
    intro Z
    rw [hH]
    ext i j
    simp [Matrix.mul_apply]
  refine ⟨U₀.submatrix id σ, ?_, d ∘ σ, hσ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have h1 := hconj 1
    rw [Matrix.mul_one] at h1
    rw [h1, Matrix.mul_one]
    have h2 : U₀ᴴ * U₀ = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp hU
      simpa [Matrix.star_eq_conjTranspose] using this
    rw [h2]
    simp
  · rw [hH]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp σ (fun i => U₀ a i * (d i : ℂ) * U₀ᴴ i b)
  · intro Z hZ
    rw [hconj Z]
    intro i j hij
    simpa using hZ (fun e => hij (σ.injective e))

end GlobalTheory.CompanionTheory.FrameSort
