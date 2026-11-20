import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS

open MeasureTheory Formalism.MainNotions.S

namespace GlobalTheory.LowestVectorDegree

/- English proof (translation)
Take `⟨hd, h⟩` from `h`. Establish `hwpos : (0 : ℝ) < ‖w‖` using `norm_pos_iff.mpr hw`. Establish `hsq : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ)`. Introduce `z`. Rewrite using `[RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Establish `h1` using `(h w w w w).2`. Simplify using `only [hsq] at h1`. Rewrite `h1` using `[integral_complex_ofReal, inner_self_eq_norm_sq_to_K]`. Establish `h2 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ)`. Rewrite using `[h1]`.

Use `push_cast`. Rewrite using `[← pow_add]`. Both sides reduce to the same expression. Establish `h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖w‖ ^ 4 / d` using `by exact_mod_cast h2`. Unfold `fdegOf`.

Rewrite using `[h3]`. Establish `h4 : ‖w‖ ^ 4 ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
theorem fdegOf_eq {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} (h : IsFdeg (Formalism.REAL.muG ε) σ d) {w : H} (hw : w ≠ 0) :
    fdegOf (Formalism.REAL.muG ε) σ w = d := by
  obtain ⟨hd, h⟩ := h
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hsq : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 := (h w w w w).2
  simp only [hsq] at h1
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
    rw [h1]
    push_cast
    rw [← pow_add]
    rfl
  have h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖w‖ ^ 4 / d := by exact_mod_cast h2
  unfold fdegOf
  rw [h3]
  have h4 : ‖w‖ ^ 4 ≠ 0 := by positivity
  field_simp

/- English proof (translation)
Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hw`. Take `⟨d, hd⟩` from `GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS n ε lam H σ hσ 1 one_pos`. Establish `hd' : IsFdeg (Formalism.REAL.muG ε) σ d` using `by simpa using hd`.

Rewrite using `[fdegOf_eq hd' hw0]`. Conclude with `hd'`.
-/
theorem isFdeg_fdegOf_of_isDS {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {w : H}
    (hw : ‖w‖ = 1) : IsFdeg (Formalism.REAL.muG ε) σ (fdegOf (Formalism.REAL.muG ε) σ w) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS n ε lam H σ hσ 1 one_pos
  have hd' : IsFdeg (Formalism.REAL.muG ε) σ d := by simpa using hd
  rw [fdegOf_eq hd' hw0]
  exact hd'

end GlobalTheory.LowestVectorDegree
