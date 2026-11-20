import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

open scoped Matrix.Norms.Operator in

/- English proof (translation)
Establish `h0 : Summable fun m : ℕ => ‖((m.factorial : ℂ)⁻¹) • A ^ m‖` using `NormedSpace.norm_expSeries_summable' A`. Establish `h1 : Summable fun k : ℕ => ‖(((2 * k).factorial : ℂ)⁻¹) • A ^ (2 * k)‖` using `h0.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simpa using h)`. Use `Summable.of_norm_bounded h1 fun k => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, norm_smul]`. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations.

Rewrite using `[norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]`. Use `inv_anti₀ (by exact_mod_cast Nat.factorial_pos _) ?_` and prove the remaining obligations. Conclude with `Nat.factorial_le (Nat.le_succ _)` after adjusting the coercions.
-/
theorem summable_sinhc_series_mat {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Summable fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) • A ^ (2 * k) := by
  have h0 : Summable fun m : ℕ => ‖((m.factorial : ℂ)⁻¹) • A ^ m‖ :=
    NormedSpace.norm_expSeries_summable' A
  have h1 : Summable fun k : ℕ => ‖(((2 * k).factorial : ℂ)⁻¹) • A ^ (2 * k)‖ :=
    h0.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simpa using h)
  refine Summable.of_norm_bounded h1 fun k => ?_
  rw [norm_smul, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  refine inv_anti₀ (by exact_mod_cast Nat.factorial_pos _) ?_
  exact_mod_cast Nat.factorial_le (Nat.le_succ _)

/- English proof (translation)
Unfold `shc`. Use `split_ifs with hx`. Substitute `hx` using the available equality. Use `hasSum_single (f := fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * (0 : ℝ) ^ (2 * k)) 0 (fun k hk => by simp [hk])` as an intermediate fact. Simplify using `using this`.

Establish `h` using `(Real.hasSum_sinh x).div_const x`. Establish `e : (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k)) = fun k : ℕ => x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) / x`. Use function extensionality and compare the values at `k`. Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem hasSum_shc_series (x : ℝ) :
    HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k)) (shc x) := by
  unfold shc
  split_ifs with hx
  · subst hx
    have := hasSum_single (f := fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * (0 : ℝ) ^ (2 * k)) 0
      (fun k hk => by simp [hk])
    simpa using this
  · have h := (Real.hasSum_sinh x).div_const x
    have e : (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k))
        = fun k : ℕ => x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) / x := by
      funext k
      rw [pow_succ]
      field_simp
    rw [e]
    exact h

/- English proof (translation)
Introduce `p q Y v x h`. Establish `hk : ∀ k : ℕ, (adMat Y ^ (2 * k)) *ᵥ v = ((x : ℂ) ^ (2 * k)) • v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Rewrite using `[mul_add, mul_one, pow_add, pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, mul_comm]`. Set `L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ (Ix p q × Ix p q → ℂ)` to `{ toFun := fun M => M *ᵥ v map_zero' := Matrix.zero_mulVec v map_add' := fun M N => Matrix.add_mulVec M N v }`. Establish `hL : Continuous L` using `continuous_id.matrix_mulVec continuous_const`. Establish `h1` using `(summable_sinhc_series_mat (adMat Y)).hasSum.map L hL`.

Establish `h2 : HasSum (fun k : ℕ => (((((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k) : ℝ) : ℂ) • v) (((shc x : ℝ) : ℂ) • v)` using `(Complex.hasSum_ofReal.2 (hasSum_shc_series x)).smul_const v`. Use `h1.unique ?_` and prove the remaining obligations. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Use `show (_ • _) *ᵥ v = _`.

Rewrite using `[Matrix.smul_mulVec, hk, smul_smul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem sinhcAd_mulVec_of_sq_eigen : ∀ (p q : ℕ) (Y : Mat p q) (v : Ix p q × Ix p q → ℂ) (x : ℝ),
    (adMat Y ^ 2) *ᵥ v = ((x : ℂ) ^ 2) • v → sinhcAd Y *ᵥ v = ((shc x : ℝ) : ℂ) • v := by
  intro p q Y v x h
  have hk : ∀ k : ℕ, (adMat Y ^ (2 * k)) *ᵥ v = ((x : ℂ) ^ (2 * k)) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [mul_add, mul_one, pow_add, pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih,
        smul_smul, mul_comm]
  let L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ (Ix p q × Ix p q → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_zero' := Matrix.zero_mulVec v
      map_add' := fun M N => Matrix.add_mulVec M N v }
  have hL : Continuous L := continuous_id.matrix_mulVec continuous_const
  have h1 := (summable_sinhc_series_mat (adMat Y)).hasSum.map L hL
  have h2 : HasSum (fun k : ℕ => (((((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k) : ℝ) : ℂ) • v)
      (((shc x : ℝ) : ℂ) • v) := (Complex.hasSum_ofReal.2 (hasSum_shc_series x)).smul_const v
  refine h1.unique ?_
  convert h2 using 1
  funext k
  show (_ • _) *ᵥ v = _
  rw [Matrix.smul_mulVec, hk, smul_smul]
  push_cast
  rfl

end GlobalTheory.PolarU
