import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.SchOp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => funext y`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Rewrite using `[iteratedDeriv_succ, ih]`.

Use function extensionality and compare the values at `y`. Establish `h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y`. Simplify using `using (hasDerivAt_id y).ofReal_comp`. Establish `h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y` using `((h1.const_mul a).cexp).const_mul (a ^ n)`. Rewrite using `[h.deriv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem iteratedDeriv_cexp_real (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

/- English proof (translation)
Use `set a : ℂ := -(2 * Real.pi * Complex.I) with ha`. Establish `e : ech = fun y : ℝ => Complex.exp (a * y)` using `rfl`. Establish `hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (a * y))` using `(contDiff_const.mul Complex.ofRealCLM.contDiff).cexp`. Use `⟨by rw [e]; exact hc, fun n => ⟨0, ‖a‖ ^ n, fun x => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[e, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real, pow_zero, mul_one, norm_mul, norm_pow]`.

Establish `h1 : ‖Complex.exp (a * x)‖ = 1`. Establish `: a * (x : ℂ) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I` using `by rw [ha]; push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`. Rewrite using `[h1, mul_one]`.
-/
theorem hasTemperateGrowth_ech : Function.HasTemperateGrowth ech := by
  set a : ℂ := -(2 * Real.pi * Complex.I) with ha
  have e : ech = fun y : ℝ => Complex.exp (a * y) := rfl
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (a * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨by rw [e]; exact hc, fun n => ⟨0, ‖a‖ ^ n, fun x => ?_⟩⟩
  rw [e, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (a * x)‖ = 1 := by
    have : a * (x : ℂ) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by rw [ha]; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

/- English proof (translation)
The claim follows from `hasTemperateGrowth_ech.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const c))`.
-/
theorem hasTemperateGrowth_ech_affine {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Y →L[ℝ] ℝ) (c : ℝ) : Function.HasTemperateGrowth (fun x : Y => ech (L x + c)) :=
  hasTemperateGrowth_ech.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const c))

/- English proof (translation)
Set `L : Y →L[ℝ] ℝ` to `LinearMap.toContinuousLinearMap (β.flip b)`. Establish `hL : ∀ x, L x = β x b` using `fun x => rfl`. Establish `hm : Function.HasTemperateGrowth (fun x : Y => ech (β x b + β a b / 2))`. Simplify `hasTemperateGrowth_ech_affine L (β a b / 2)` using `only [hL]`. Establish `ht : Function.HasTemperateGrowth (fun x : Y => x + a)` using `Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a)`.

Establish `hu : ∃ (k : ℕ) (C : ℝ), ∀ x : Y, ‖x‖ ≤ C * (1 + ‖x + a‖) ^ k`. Use `⟨1, 1 + ‖a‖, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖x‖ ≤ ‖x + a‖ + ‖a‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `norm_nonneg (x + a)`.

Establish `h3` using `norm_nonneg a`. Rewrite using `[pow_one]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨SchwartzMap.smulLeftCLM ℂ (fun x : Y => ech (β x b + β a b / 2)) (SchwartzMap.compCLM ℂ ht hu f), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply hm, SchwartzMap.compCLM_apply]`. Simplify using `[sch, smul_eq_mul]`.
-/
theorem sch_schwartz {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : SchwartzMap Y ℂ) : ∃ g : SchwartzMap Y ℂ, ⇑g = sch β a b ⇑f := by
  let L : Y →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (β.flip b)
  have hL : ∀ x, L x = β x b := fun x => rfl
  have hm : Function.HasTemperateGrowth (fun x : Y => ech (β x b + β a b / 2)) := by
    simpa only [hL] using hasTemperateGrowth_ech_affine L (β a b / 2)
  have ht : Function.HasTemperateGrowth (fun x : Y => x + a) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a)
  have hu : ∃ (k : ℕ) (C : ℝ), ∀ x : Y, ‖x‖ ≤ C * (1 + ‖x + a‖) ^ k := by
    refine ⟨1, 1 + ‖a‖, fun x => ?_⟩
    have h1 : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
      calc ‖x‖ = ‖(x + a) - a‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
    have h2 := norm_nonneg (x + a)
    have h3 := norm_nonneg a
    rw [pow_one]
    nlinarith
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : Y => ech (β x b + β a b / 2)) (SchwartzMap.compCLM ℂ ht hu f), ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hm, SchwartzMap.compCLM_apply]
  simp [sch, smul_eq_mul]

end GlobalTheory.SchOp
