import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory
open IsDedekindDomain
open scoped TensorProduct

/- English proof (translation)
Use `set σ := sg (FiniteAdeleRing (𝓞 F) F) c with hσ`. Use `set G' : Matrix (Fin r) (Fin r) (RA F E) := G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) with hG'`. Establish `hM : gᵀ * G' * g.map σ = G'`. Use extensionality with `a b`. Establish `h` using `hg.2 (Pi.single a 1) (Pi.single b 1)`.

Simplify using `only [hermA, Matrix.mulVec_single_one] at h`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Both sides reduce to the same expression. Simplify using `[G', Pi.single_apply, apply_ite σ]`. Establish `hdet` using `congrArg Matrix.det hM`. Establish `hs : (g.map σ).det = σ g.det`. Rewrite using `[show g.map σ = (σ : RA F E →+* RA F E).mapMatrix g from rfl, ← RingHom.map_det]`.

Both sides reduce to the same expression. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs]`. Establish `hG'det : G'.det = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det`. Rewrite using `[hG', show G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) = ((Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) : E →+* RA F E).mapMatrix G from rfl, ← RingHom.map_det]`. Both sides reduce to the same expression.

Establish `hu : IsUnit G'.det`. Rewrite using `[hG'det]`. Use `IsUnit.of_mul_eq_one ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det⁻¹) ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hG]`. Both sides reduce to the same expression.

Unfold `IsTA`. Establish `: g.det * σ g.det * G'.det = 1 * G'.det`. Rewrite using `[one_mul]`. Use `hdet using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Conclude with `hu.mul_right_cancel this`.
-/
theorem isTA_det_of_isUA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {r : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA F E))
    (hG : G.det ≠ 0) (hg : IsUA c G g) : IsTA c g.det := by
  set σ := sg (FiniteAdeleRing (𝓞 F) F) c with hσ
  set G' : Matrix (Fin r) (Fin r) (RA F E) := G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) with hG'
  have hM : gᵀ * G' * g.map σ = G' := by
    ext a b
    have h := hg.2 (Pi.single a 1) (Pi.single b 1)
    simp only [hermA, Matrix.mulVec_single_one] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    convert h using 1
    · rfl
    · simp [G', Pi.single_apply, apply_ite σ]
  have hdet := congrArg Matrix.det hM
  have hs : (g.map σ).det = σ g.det := by
    rw [show g.map σ = (σ : RA F E →+* RA F E).mapMatrix g from rfl, ← RingHom.map_det]; rfl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs] at hdet
  have hG'det : G'.det = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det := by
    rw [hG', show G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) =
      ((Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) : E →+* RA F E).mapMatrix G from rfl,
      ← RingHom.map_det]; rfl
  have hu : IsUnit G'.det := by
    rw [hG'det]
    refine IsUnit.of_mul_eq_one ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det⁻¹) ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hG]
    rfl
  unfold IsTA
  have : g.det * σ g.det * G'.det = 1 * G'.det := by
    rw [one_mul]; convert hdet using 1; ring
  exact hu.mul_right_cancel this

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ hG hg` and use `isTA_det_of_isUA _ _ _ hG hg`.
-/
theorem unitary_det_isTA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), G.det ≠ 0 → IsUA (IsCMField.complexConj E) G g → IsTA (IsCMField.complexConj E) g.det :=
  fun _ _ _ _ _ _ _ hG hg => isTA_det_of_isUA _ _ _ hG hg

end GlobalTheory
