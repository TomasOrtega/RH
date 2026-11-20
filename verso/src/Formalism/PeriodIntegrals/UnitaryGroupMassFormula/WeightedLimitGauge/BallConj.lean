import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Unimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.UnimodS

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim HU

variable {m : ℕ}

def realE (X : Matrix (Fin m) (Fin m) ℂ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  (WithLp.equiv 2 _).symm (realifyFun X)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realE_apply (X : Matrix (Fin m) (Fin m) ℂ) (p : Fin m × Fin m × Bool) :
    realE X p = realifyFun X p := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `only [unrealify, realE_apply, realifyFun]`. Simplify using the standard rewrite rules.
-/
theorem unr_realE (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (realE X) = X := by
  funext i j
  simp only [unrealify, realE_apply, realifyFun]
  simp

/- English proof (translation)
Use extensionality with `⟨i, j, b⟩`. Rewrite using `[realE_apply]`. Apply the tactic sequence `cases b <;> simp [realifyFun, unrealify]`.
-/
theorem realE_unr (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : realE (unrealify x) = x := by
  ext ⟨i, j, b⟩
  rw [realE_apply]
  cases b <;> simp [realifyFun, unrealify]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify]`.
-/
theorem unr_add (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  funext i j
  apply Complex.ext <;> simp [unrealify]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify]`.
-/
theorem unr_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  funext i j
  apply Complex.ext <;> simp [unrealify]

/- English proof (translation)
Use extensionality with `⟨i, j, b⟩`. Apply the tactic sequence `cases b <;> simp [realE_apply, realifyFun]`.
-/
theorem realE_add (X Y : Matrix (Fin m) (Fin m) ℂ) : realE (X + Y) = realE X + realE Y := by
  ext ⟨i, j, b⟩
  cases b <;> simp [realE_apply, realifyFun]

/- English proof (translation)
Use extensionality with `⟨i, j, b⟩`. Apply the tactic sequence `cases b <;> simp [realE_apply, realifyFun]`.
-/
theorem realE_smul (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : realE ((c : ℂ) • X) = c • realE X := by
  ext ⟨i, j, b⟩
  cases b <;> simp [realE_apply, realifyFun]

def conjL (q : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := realE (q * unrealify x * q⁻¹)
  map_add' x y := by rw [unr_add, Matrix.mul_add, Matrix.add_mul, realE_add]
  map_smul' c x := by
    rw [unr_smul, Matrix.mul_smul, Matrix.smul_mul, realE_smul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjL_apply (q : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    conjL q x = realE (q * unrealify x * q⁻¹) := rfl

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Use `congr 1`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool]`. Simplify using `only [realE_apply, realifyFun, Real.norm_eq_abs, sq_abs, if_true, Bool.false_eq_true, if_false, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_realE (X : Matrix (Fin m) (Fin m) ℂ) :
    ‖realE X‖ = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [realE_apply, realifyFun, Real.norm_eq_abs, sq_abs, if_true, Bool.false_eq_true, if_false,
    Complex.normSq_apply]
  ring

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_conj]`.
-/
theorem frob_trace (X : Matrix (Fin m) (Fin m) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (X i j) : ℝ) : ℂ) = (X * Xᴴ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj]

/- English proof (translation)
Establish `hqi : q⁻¹ = qᴴ` using `Matrix.inv_eq_left_inv hq`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[frob_trace, frob_trace, hqi]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = (X * Xᴴ * (qᴴ * q)).trace := by`. Rewrite using `[hq, Matrix.mul_one, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hq, Matrix.one_mul]`. Use `_ = (X * Xᴴ).trace := by rw [hq, Matrix.mul_one]`.
-/
theorem frob_conj (q X : Matrix (Fin m) (Fin m) ℂ) (hq : qᴴ * q = 1) :
    ∑ i, ∑ j, Complex.normSq ((q * X * q⁻¹) i j) = ∑ i, ∑ j, Complex.normSq (X i j) := by
  have hqi : q⁻¹ = qᴴ := Matrix.inv_eq_left_inv hq
  apply Complex.ofReal_injective
  rw [frob_trace, frob_trace, hqi]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc (q * X * qᴴ * (q * (Xᴴ * qᴴ))).trace = (q * (X * (qᴴ * q) * Xᴴ) * qᴴ).trace := by
        simp only [Matrix.mul_assoc]
    _ = (X * Xᴴ * (qᴴ * q)).trace := by
        rw [hq, Matrix.mul_one, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hq, Matrix.one_mul]
    _ = (X * Xᴴ).trace := by rw [hq, Matrix.mul_one]

/- English proof (translation)
Introduce `t`. Establish `hu` using `uwb_unit hq`. Establish `e : (t : ℂ) • (q * X * q⁻¹) = q * ((t : ℂ) • X) * q⁻¹`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[e, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu)]`.

Conclude with `uwb_mul (uwb_mul hq (hX t)) (uwb_inv hq)`.
-/
theorem conj_lieOf {k r : ℕ} (q : Mat k r) (hq : q ∈ UWb k r) (X : Mat k r) (hX : X ∈ lieOf (UWb k r)) :
    q * X * q⁻¹ ∈ lieOf (UWb k r) := by
  intro t
  have hu := uwb_unit hq
  have e : (t : ℂ) • (q * X * q⁻¹) = q * ((t : ℂ) • X) * q⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu)]
  exact uwb_mul (uwb_mul hq (hX t)) (uwb_inv hq)

/- English proof (translation)
Introduce `k r ρ q hq hqu x hx`. Establish `hu` using `uwb_unit hq`. Take `⟨v, hv, hvx⟩` from `hx`. Establish `hmap : Submodule.map (conjL q) (lieE (UWb k r)) ≤ lieE (UWb k r)`. Rewrite using `[lieE, Submodule.map_span]`.

Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨X, hX, rfl⟩, rfl⟩`. Use `⟨q * X * q⁻¹, conj_lieOf q hq X hX, ?_⟩` and prove the remaining obligations. Use `show realE (q * X * q⁻¹) = conjL q (realE X)`. Rewrite using `[conjL_apply, unr_realE]`.

Establish `hmem : conjL q (v : EuclideanSpace ℝ _) ∈ lieE (UWb k r)` using `hmap ⟨v, v.2, rfl⟩`. Use `⟨⟨conjL q v, hmem⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_zero_right] at hv ⊢ show ‖conjL q (v : EuclideanSpace ℝ _)‖ < ρ`. Rewrite using `[conjL_apply, norm_realE, frob_conj q _ hqu, ← norm_realE, realE_unr]`. Conclude with `hv`.

Establish `hx' : (Matrix.of x : Mat k r) * q = NormedSpace.exp (unrealify (v : EuclideanSpace ℝ _))`. Use `congrArg (fun f : Mt k r => (Matrix.of f : Mat k r)) hvx` as an intermediate fact. Conclude with `this.symm`. Use `show (fun i j => NormedSpace.exp (unrealify (conjL q (v : EuclideanSpace ℝ _))) i j) = q * Matrix.of x`. Rewrite using `[conjL_apply, unr_realE, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu), ← hx']`.

Use function extensionality and compare the values at `i j`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`.
-/
theorem ballConj : BallConj := by
  intro k r ρ q hq hqu x hx
  have hu := uwb_unit hq
  obtain ⟨v, hv, hvx⟩ := hx

  have hmap : Submodule.map (conjL q) (lieE (UWb k r)) ≤ lieE (UWb k r) := by
    rw [lieE, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨q * X * q⁻¹, conj_lieOf q hq X hX, ?_⟩
    show realE (q * X * q⁻¹) = conjL q (realE X)
    rw [conjL_apply, unr_realE]
  have hmem : conjL q (v : EuclideanSpace ℝ _) ∈ lieE (UWb k r) :=
    hmap ⟨v, v.2, rfl⟩
  refine ⟨⟨conjL q v, hmem⟩, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    show ‖conjL q (v : EuclideanSpace ℝ _)‖ < ρ
    rw [conjL_apply, norm_realE, frob_conj q _ hqu, ← norm_realE, realE_unr]
    exact hv
  · have hx' : (Matrix.of x : Mat k r) * q = NormedSpace.exp (unrealify (v : EuclideanSpace ℝ _)) := by
      have := congrArg (fun f : Mt k r => (Matrix.of f : Mat k r)) hvx
      exact this.symm
    show (fun i j => NormedSpace.exp (unrealify (conjL q (v : EuclideanSpace ℝ _))) i j) =
      q * Matrix.of x
    rw [conjL_apply, unr_realE, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu), ← hx']
    funext i j
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end PI.RhsWLim.W
