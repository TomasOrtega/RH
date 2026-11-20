import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.MeanDual

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def invT (g : MatInf E j) : MatInf E j := fun w a b => (Matrix.of (g w))⁻¹ b a

def trDual (Λ : Submodule (𝓞 E) (Fin j → E)) : Submodule (𝓞 E) (Fin j → E) where
  carrier := {y | ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z, hz⟩ := ha x hx
    obtain ⟨z', hz'⟩ := hb x hx
    exact ⟨z + z', by rw [dotProduct_add, map_add, hz, hz']; push_cast; ring⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨z, hz⟩ := hy (c • x) (Λ.smul_mem c hx)
    refine ⟨z, ?_⟩
    rw [← hz, dotProduct_smul, smul_dotProduct]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_trDual {Λ : Submodule (𝓞 E) (Fin j → E)} {y : Fin j → E} :
    y ∈ trDual E j Λ ↔ ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ) := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_invT (g : MatInf E j) (w : InfinitePlace E) :
    Matrix.of (invT E j g w) = ((Matrix.of (g w))⁻¹)ᵀ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_mul (g h : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((g * h) w) = Matrix.of (g w) * Matrix.of (h w) := rfl

/- English proof (translation)
The claim follows from `funext fun w => Matrix.of.injective (H w)`.
-/
theorem matInf_ext {g h : MatInf E j} (H : ∀ w, Matrix.of (g w) = Matrix.of (h w)) : g = h :=
  funext fun w => Matrix.of.injective (H w)

/- English proof (translation)
Unfold `detNorm`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Rewrite `h` using `[Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])]`. Conclude with `lt_irrefl _ h`.

Introduce `h`. Conclude with `Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2`.
-/
theorem detNorm_pos_iff (g : MatInf E j) :
    0 < detNorm E j g ↔ ∀ w, (Matrix.of (g w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

/- English proof (translation)
Apply `matInf_ext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[of_invT, of_mul, of_mul, of_invT, of_invT, Matrix.mul_inv_rev, Matrix.transpose_mul]`.
-/
theorem invT_mul (g h : MatInf E j) : invT E j (g * h) = invT E j g * invT E j h := by
  apply matInf_ext
  intro w
  rw [of_invT, of_mul, of_mul, of_invT, of_invT, Matrix.mul_inv_rev, Matrix.transpose_mul]

/- English proof (translation)
Simplify using `only [detNorm_pos_iff, of_invT, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ne_eq, inv_eq_zero]`.
-/
theorem detNorm_invT_pos_iff (g : MatInf E j) :
    0 < detNorm E j (invT E j g) ↔ 0 < detNorm E j g := by
  simp only [detNorm_pos_iff, of_invT, Matrix.det_transpose, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', ne_eq, inv_eq_zero]

/- English proof (translation)
Apply `matInf_ext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[of_invT, of_invT, ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j g).1 hg w))]`.
-/
theorem invT_invT {g : MatInf E j} (hg : 0 < detNorm E j g) : invT E j (invT E j g) = g := by
  apply matInf_ext
  intro w
  rw [of_invT, of_invT, ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j g).1 hg w))]

/- English proof (translation)
Unfold `detNorm`. Simplify using `only [of_mul, Matrix.det_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]`.
-/
theorem detNorm_mul (g h : MatInf E j) : detNorm E j (g * h) = detNorm E j g * detNorm E j h := by
  unfold detNorm
  simp only [of_mul, Matrix.det_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]

/- English proof (translation)
Unfold `detNorm`. Use `continuous_finsetProd _ fun w _ => ?_` and prove the remaining obligations. Use `Continuous.pow (Continuous.norm ?_) 2` and prove the remaining obligations. Conclude with `Continuous.matrix_det (A := fun g : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (g w)) (continuous_apply w)`.
-/
theorem continuous_detNorm :
    Continuous (fun g : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j g) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  refine Continuous.pow (Continuous.norm ?_) 2
  exact Continuous.matrix_det (A := fun g : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (g w))
    (continuous_apply w)

/- English proof (translation)
The claim follows from `(isOpen_lt continuous_const (continuous_detNorm E j)).measurableSet`.
-/
theorem measurableSet_detNorm_pos : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
  (isOpen_lt continuous_const (continuous_detNorm E j)).measurableSet

end GlobalTheory.MeanDual
