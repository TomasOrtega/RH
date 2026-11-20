import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

/- English proof (translation)
Simplify using `[Matrix.vecMul, dotProduct, Complex.re_sum]`.
-/
lemma flatcoord_re_vecMul {g : ℕ} (p : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (i : Fin g) :
    (((fun k => (p k : ℂ)) ᵥ* τ) i).re = (p ᵥ* τ.map Complex.re) i := by
  simp [Matrix.vecMul, dotProduct, Complex.re_sum]

/- English proof (translation)
Simplify using `[Matrix.vecMul, dotProduct, Complex.im_sum]`.
-/
lemma flatcoord_im_vecMul {g : ℕ} (p : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (i : Fin g) :
    (((fun k => (p k : ℂ)) ᵥ* τ) i).im = (p ᵥ* τ.map Complex.im) i := by
  simp [Matrix.vecMul, dotProduct, Complex.im_sum]

/- English proof (translation)
Establish `hu : IsUnit (τ.map Complex.im).det` using `h.det_pos.ne'.isUnit`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Establish `him : (fun i => (per τ x i).im) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im`. Use function extensionality and compare the values at `i`.

Simplify using `[per, flatcoord_im_vecMul]`. Establish `hre : (fun i => (per τ x i).re) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.re + fun i => x (Sum.inr i)`. Use function extensionality and compare the values at `i`. Simplify using `[per, flatcoord_re_vecMul]`. Establish `hp : (fun i => (per τ x i).im) ᵥ* (τ.map Complex.im)⁻¹ = fun i => x (Sum.inl i)`.

Rewrite using `[him, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]`. Use function extensionality and compare the values at `k`. Break down `k with i | i` into its components or cases. Simplify using `only [flatOf, Sum.elim_inl, hp]`. Simplify using `only [flatOf, Sum.elim_inr, hp, hre]`.

Simplify using the standard rewrite rules. Introduce `z set p := (fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹ with hpdef`. Establish `hp : p ᵥ* τ.map Complex.im = fun i => (z i).im`. Rewrite using `[hpdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]`. Use function extensionality and compare the values at `i`.

Apply `Complex.ext` to reduce the goal to its premises. Use `flatcoord_re_vecMul p τ i` as an intermediate fact. Simplify using `only [per, flatOf, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Complex.add_re, Complex.ofReal_re, ← hpdef, this, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `flatcoord_im_vecMul p τ i` as an intermediate fact.

Simplify using `only [per, flatOf, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Complex.add_im, Complex.ofReal_im, ← hpdef, this, hp]`. Simplify using the standard rewrite rules.
-/
theorem flatOf_per_inv {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (h : (τ.map Complex.im).PosDef) :
    (∀ x, flatOf τ (per τ x) = x) ∧ ∀ z, per τ (flatOf τ z) = z := by
  have hu : IsUnit (τ.map Complex.im).det := h.det_pos.ne'.isUnit
  constructor
  · intro x
    have him : (fun i => (per τ x i).im) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im := by
      funext i; simp [per, flatcoord_im_vecMul]
    have hre : (fun i => (per τ x i).re) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.re +
        fun i => x (Sum.inr i) := by
      funext i; simp [per, flatcoord_re_vecMul]
    have hp : (fun i => (per τ x i).im) ᵥ* (τ.map Complex.im)⁻¹ = fun i => x (Sum.inl i) := by
      rw [him, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    funext k
    rcases k with i | i
    · simp only [flatOf, Sum.elim_inl, hp]
    · simp only [flatOf, Sum.elim_inr, hp, hre]
      simp
  · intro z
    set p := (fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹ with hpdef
    have hp : p ᵥ* τ.map Complex.im = fun i => (z i).im := by
      rw [hpdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
    funext i
    apply Complex.ext
    · have := flatcoord_re_vecMul p τ i
      simp only [per, flatOf, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Complex.add_re,
        Complex.ofReal_re, ← hpdef, this, Pi.sub_apply]
      ring
    · have := flatcoord_im_vecMul p τ i
      simp only [per, flatOf, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Complex.add_im,
        Complex.ofReal_im, ← hpdef, this, hp]
      simp

/- English proof (translation)
Introduce `g E _ _ _ B τ hτ b hb`. Conclude with `flatOf_per_inv (τ b) (hτ.2.2 b hb).2`.
-/
theorem flatcoord_inverse : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ b ∈ B, (∀ x, flatOf (τ b) (per (τ b) x) = x) ∧ ∀ z, per (τ b) (flatOf (τ b) z) = z := by
  intro g E _ _ _ B τ hτ b hb
  exact flatOf_per_inv (τ b) (hτ.2.2 b hb).2

end GlobalTheory
