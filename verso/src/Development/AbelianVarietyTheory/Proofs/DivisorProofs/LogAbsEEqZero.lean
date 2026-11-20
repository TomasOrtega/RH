import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.CtTyp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def ctf {d d₁ : ℕ} {W : Spc F E d} (H' : Plane E d d₁) (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H'))
    (f : UA σ W.J → ℂ) (g : UA σ W.J) : ℂ :=
  ∫ u in 𝓕, f (u.1 * g) ∂μ

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem absE_pos (t : (AE F E)ˣ) : 0 < (absE F E t : ℝ) := by
  have h : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h0 : absE F E t ≠ 0 := left_ne_zero_of_mul_eq_one h
  exact_mod_cast pos_iff_ne_zero.2 h0

def twAbs (χ : Chr F E) (s : ℝ) : (AE F E)ˣ →* ℂˣ where
  toFun t := Units.mk0 ((χ t : ℂ) * (((absE F E t : ℝ) ^ s : ℝ) : ℂ))
    (mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (absE_pos t) s).ne'))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Units.val_mul, Units.val_mk0]
    rw [Real.mul_rpow (absE_pos x).le (absE_pos y).le]
    push_cast
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_twAbs (χ : Chr F E) (s : ℝ) (t : (AE F E)ˣ) :
    ((twAbs χ s t : ℂˣ) : ℂ) = (χ t : ℂ) * (((absE F E t : ℝ) ^ s : ℝ) : ℂ) := rfl

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
example : twAbs (1 : Chr F E) 0 = 1 := by ext t; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem norm_twAbs (χ : Chr F E) (s : ℝ) (t : (AE F E)ˣ) : ‖((twAbs χ s t : ℂˣ) : ℂ)‖ = (absE F E t : ℝ) ^ s := by
  rw [coe_twAbs, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (absE_pos t) s)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem log_absE_mul (x y : (AE F E)ˣ) :
    Real.log (absE F E (x * y) : ℝ) = Real.log (absE F E x : ℝ) + Real.log (absE F E y : ℝ) := by
  rw [map_mul, NNReal.coe_mul, Real.log_mul (absE_pos x).ne' (absE_pos y).ne']

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem log_absE_eq_zero {t : (AE F E)ˣ} : Real.log (absE F E t : ℝ) = 0 ↔ absE F E t = 1 := by
  constructor
  · intro h
    have := Real.exp_log (absE_pos t)
    rw [h, Real.exp_zero] at this
    exact_mod_cast this.symm
  · intro h; rw [h]; simp

end GlobalTheory.CtTyp
