import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineEigenvalue
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVecAtNeZero

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def LineEigenvalue.coordRatio (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (i : InfinitePlace E → ι) (g : archUnitary h v) (w : InfinitePlace E) : ℂ :=
  ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) (i w)) / vecAt v x₀ w (i w)

omit [NumberField E] in

/- English proof (translation)
Unfold `coordRatio`. Use `Continuous.div_const ?_ _` and prove the remaining obligations. Conclude with `(continuous_apply (i w)).comp ((Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec continuous_const)`.
-/
theorem LineEigenvalue.continuous_coordRatio (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (i : InfinitePlace E → ι) (w : InfinitePlace E) :
    Continuous fun g : archUnitary h v => coordRatio h v x₀ i g w := by
  unfold coordRatio
  refine Continuous.div_const ?_ _
  exact (continuous_apply (i w)).comp
    ((Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
      continuous_const)

omit [NumberField E] in

/- English proof (translation)
Take `⟨c, hc⟩` from `hg w`. Establish `e : coordRatio h v x₀ i g w = c`. Rewrite using `[coordRatio, hc, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self (hi w), mul_one]`. Rewrite using `[e, hc]`.
-/
theorem LineEigenvalue.mulVec_eq_coordRatio {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {i : InfinitePlace E → ι} (hi : ∀ w, vecAt v x₀ w (i w) ≠ 0) {g : archUnitary h v}
    (hg : g ∈ lineStab h v x₀) (w : InfinitePlace E) :
    ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      coordRatio h v x₀ i g w • vecAt v x₀ w := by
  obtain ⟨c, hc⟩ := hg w
  have e : coordRatio h v x₀ i g w = c := by
    rw [coordRatio, hc, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self (hi w), mul_one]
  rw [e, hc]

/- English proof (translation)
Introduce `h0`. Establish `e` using `mulVec_eq_coordRatio hi hg w`. Rewrite `e` using `[h0, zero_smul]`. Apply `hi w` to reduce the goal to its premises. Establish `hX : vecAt v x₀ w = (((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w))`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[hX, e, Matrix.mulVec_zero, Pi.zero_apply]`.
-/
theorem LineEigenvalue.coordRatio_ne_zero {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {i : InfinitePlace E → ι} (hi : ∀ w, vecAt v x₀ w (i w) ≠ 0) {g : archUnitary h v}
    (hg : g ∈ lineStab h v x₀) (w : InfinitePlace E) : coordRatio h v x₀ i g w ≠ 0 := by
  intro h0
  have e := mulVec_eq_coordRatio hi hg w
  rw [h0, zero_smul] at e
  apply hi w
  have hX : vecAt v x₀ w = (((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ
      (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w)) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hX, e, Matrix.mulVec_zero, Pi.zero_apply]

/- English proof (translation)
Introduce `x₀ hx₀`. Establish `hne : ∀ w, ∃ j, vecAt v x₀ w j ≠ 0` using `fun w => by`. Simplify using `using Function.ne_iff.mp (h1 x₀ hx₀ w)`. Use `choose i hi using hne`. Use `⟨fun p w => Units.mk0 (coordRatio h v x₀ i (p : archUnitary h v) w) (coordRatio_ne_zero hi p.2 w), ?_, fun p w => ?_⟩` and prove the remaining obligations.

Use `continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(continuous_coordRatio h v x₀ i w).comp continuous_subtype_val`. Simplify using `only [Units.val_inv_eq_inv_val, Units.val_mk0]`. Conclude with `((continuous_coordRatio h v x₀ i w).comp continuous_subtype_val).inv₀ fun p => coordRatio_ne_zero hi p.2 w`. Rewrite using `[Units.val_mk0]`.

Conclude with `mulVec_eq_coordRatio hi p.2 w`.
-/
theorem LineEigenvalue.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : VecAtNeZero.Statement v) : LineEigenvalue.Statement h v := by
  intro x₀ hx₀
  have hne : ∀ w, ∃ j, vecAt v x₀ w j ≠ 0 := fun w => by
    simpa using Function.ne_iff.mp (h1 x₀ hx₀ w)
  choose i hi using hne
  refine ⟨fun p w => Units.mk0 (coordRatio h v x₀ i (p : archUnitary h v) w)
    (coordRatio_ne_zero hi p.2 w), ?_, fun p w => ?_⟩
  · refine continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_coordRatio h v x₀ i w).comp continuous_subtype_val
    · simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
      exact ((continuous_coordRatio h v x₀ i w).comp continuous_subtype_val).inv₀
        fun p => coordRatio_ne_zero hi p.2 w
  · rw [Units.val_mk0]
    exact mulVec_eq_coordRatio hi p.2 w

/- English proof (translation)
The claim follows from `LineEigenvalue.proof h v (VecAtNeZero.proof v)`.
-/
theorem LineEigenvalue.closed (h : HermitianForm F E W) (v : Basis ι E W) :
    LineEigenvalue.Statement h v :=
  LineEigenvalue.proof h v (VecAtNeZero.proof v)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
