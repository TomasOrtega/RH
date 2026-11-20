import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped Matrix ComplexConjugate ENNReal
open MeasureTheory

noncomputable section

namespace FSInv

open CP

/- English proof (translation)
Introduce `N U`. Use `set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) with hA`. Establish `hU : star A * A = 1` using `Matrix.mem_unitaryGroup_iff'.mp U.2`. Establish `hC : ∀ w : Fin (N + 1) → ℂ, ((normSq2 w : ℝ) : ℂ) = star w ⬝ᵥ w`. Introduce `w`.

Simplify using `only [normSq2, dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression. Establish `hnorm : ∀ v : Fin (N + 1) → ℂ, normSq2 (A *ᵥ v) = normSq2 v`. Introduce `v`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[hC, hC, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose, hU, Matrix.vecMul_one]`. Establish `hdens : ∀ v : Fin (N + 1) → ℂ, ambDensity (A *ᵥ v) = ambDensity v`. Introduce `v`. Simplify using `only [ambDensity, hnorm]`.

Establish `hdet : Complex.normSq (LinearMap.det (Matrix.toLin' A)) = 1`. Rewrite using `[LinearMap.det_toLin']`. Establish `h1 : star A.det * A.det = 1` using `Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary U.2)`. Establish `h2 : ((Complex.normSq A.det : ℝ) : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`.

Conclude with `h1`. Conclude with `h2` after adjusting the coercions. Establish `hdet0 : LinearMap.det (Matrix.toLin' A) ≠ 0`. Introduce `h`. Rewrite `hdet` using `[h, map_zero]`.

Conclude with `zero_ne_one hdet`. Establish `hT : Measurable (Matrix.toLin' A)` using `(LinearMap.continuous_of_finiteDimensional (Matrix.toLin' A)).measurable`. Establish `hmd : Measurable fun v : Fin (N + 1) → ℂ => ENNReal.ofReal (ambDensity v)`. Unfold `ambDensity normSq2`. Use `fun_prop`.

Use `Measure.ext_of_lintegral _ fun f hf => ?_` and prove the remaining obligations. Rewrite using `[lintegral_map hf hT, ambMeasure, lintegral_withDensity_eq_lintegral_mul _ hmd (show Measurable fun a => f (Matrix.toLin' A a) from hf.comp hT), lintegral_withDensity_eq_lintegral_mul _ hmd hf]`. Establish `key` using `hL (N + 1) (Matrix.toLin' A) hdet0 (fun u => ENNReal.ofReal (ambDensity u) * f u) (hmd.mul hf)`. Rewrite `key` using `[hdet, ENNReal.ofReal_one, one_mul]`. Simplify using `only [Pi.mul_apply, Matrix.toLin'_apply] at key ⊢`.

Rewrite using `[key]`. Simplify using `only [hdens]`.
-/
theorem AmbUnitary.proof (hL : LinChange.Statement) : AmbUnitary.Statement := by
  intro N U
  set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) with hA
  have hU : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2

  have hC : ∀ w : Fin (N + 1) → ℂ, ((normSq2 w : ℝ) : ℂ) = star w ⬝ᵥ w := by
    intro w
    simp only [normSq2, dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast; rfl
  have hnorm : ∀ v : Fin (N + 1) → ℂ, normSq2 (A *ᵥ v) = normSq2 v := by
    intro v
    apply Complex.ofReal_injective
    rw [hC, hC, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.vecMul_one]
  have hdens : ∀ v : Fin (N + 1) → ℂ, ambDensity (A *ᵥ v) = ambDensity v := by
    intro v; simp only [ambDensity, hnorm]

  have hdet : Complex.normSq (LinearMap.det (Matrix.toLin' A)) = 1 := by
    rw [LinearMap.det_toLin']
    have h1 : star A.det * A.det = 1 := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary U.2)
    have h2 : ((Complex.normSq A.det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]; exact h1
    exact_mod_cast h2
  have hdet0 : LinearMap.det (Matrix.toLin' A) ≠ 0 := by
    intro h; rw [h, map_zero] at hdet; exact zero_ne_one hdet
  have hT : Measurable (Matrix.toLin' A) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.toLin' A)).measurable
  have hmd : Measurable fun v : Fin (N + 1) → ℂ => ENNReal.ofReal (ambDensity v) := by
    unfold ambDensity normSq2; fun_prop
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf hT, ambMeasure, lintegral_withDensity_eq_lintegral_mul _ hmd
      (show Measurable fun a => f (Matrix.toLin' A a) from hf.comp hT),
    lintegral_withDensity_eq_lintegral_mul _ hmd hf]
  have key := hL (N + 1) (Matrix.toLin' A) hdet0 (fun u => ENNReal.ofReal (ambDensity u) * f u)
    (hmd.mul hf)
  rw [hdet, ENNReal.ofReal_one, one_mul] at key
  simp only [Pi.mul_apply, Matrix.toLin'_apply] at key ⊢
  rw [key]
  simp only [hdens]

end FSInv

end

end GroundTheory.Heights₂.Heights
