import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.AdmissibleFunctionClassClosureProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.QuadraticFormGradientFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments
import Mathlib.Analysis.Calculus.SmoothSeries
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_` and prove the remaining obligations. Establish `h : (v ᵥ* Matrix.of Z) j = ∑ i, v i * Z i j` using `rfl`. Rewrite using `[h]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `h2 : ∀ i ∈ (Finset.univ : Finset (Fin a)), ‖v i * Z i j‖ ≤ ‖v‖ * ‖Z‖` using `fun i _ => (norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm v i) ((norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i)) (norm_nonneg _) (norm_nonneg _))`.

Use `(Finset.sum_le_sum h2).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `[mul_assoc]`.
-/
private theorem vm_le (v : Fin a → Cinf E) (Z : Lie E a) : ‖v ᵥ* Matrix.of Z‖ ≤ a * ‖v‖ * ‖Z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have h : (v ᵥ* Matrix.of Z) j = ∑ i, v i * Z i j := rfl
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin a)), ‖v i * Z i j‖ ≤ ‖v‖ * ‖Z‖ := fun i _ =>
    (norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm v i)
      ((norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i)) (norm_nonneg _) (norm_nonneg _))
  refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
  simp [mul_assoc]

private noncomputable def vmL (v : Fin a → Cinf E) : Lie E a →L[ℝ] (Fin a → Cinf E) :=
  LinearMap.mkContinuous
    { toFun := fun Z => v ᵥ* Matrix.of Z
      map_add' := fun Z W => Matrix.vecMul_add (Matrix.of Z) (Matrix.of W) v
      map_smul' := fun c Z => by
        ext j w
        simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_left_comm] }
    (a * ‖v‖) (fun Z => vm_le v Z)

/- English proof (translation)
The claim follows from `LinearMap.mkContinuous_norm_le _ (by positivity) _`.
-/
private theorem vmL_norm (v : Fin a → Cinf E) : ‖vmL v‖ ≤ a * ‖v‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/- English proof (translation)
Take `⟨u, hu⟩` from `hy`. Use `set B : ℝ := a * ‖toL (u⁻¹).val‖ with hB`. Establish `hB0 : 0 ≤ B` using `by positivity`. Establish `ha : (0:ℝ) ≤ a` using `Nat.cast_nonneg a`. Establish `hp : 0 < 2 * (B * a + 1)` using `by positivity`.

Use `⟨1 / (2 * (B * a + 1)), 2 * B, by positivity, by positivity, fun z hz v => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖v‖ ≤ B * ‖v ᵥ* Matrix.of y‖`. Establish `h` using `vm_le (v ᵥ* Matrix.of y) (toL (u⁻¹).val)`. Establish `e : (v ᵥ* Matrix.of y) ᵥ* Matrix.of (toL (u⁻¹).val) = v`. Rewrite using `[Matrix.vecMul_vecMul, ← hu]`.

Express the relevant statement in the definitionally equal form `v ᵥ* (u.val * (u⁻¹).val) = v`. Rewrite using `[Units.mul_inv, Matrix.vecMul_one]`. Rewrite `h` using `[e]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : v ᵥ* Matrix.of y = v ᵥ* Matrix.of z + v ᵥ* Matrix.of (y - z)`.

Use `(vmL v).map_add z (y - z)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Conclude with `this`. Establish `h3 : ‖y - z‖ * (2 * (B * a + 1)) ≤ 1`. Rewrite `hz` using `[Metric.mem_ball, dist_comm, dist_eq_norm, lt_div_iff₀ hp]`.

Conclude with `hz.le`. Establish `h4 : ‖v ᵥ* Matrix.of y‖ ≤ ‖v ᵥ* Matrix.of z‖ + a * ‖v‖ * ‖y - z‖`. Rewrite using `[h2]`. Conclude with `(norm_add_le _ _).trans (by gcongr; exact vm_le v _)`. Establish `h5` using `mul_le_mul_of_nonneg_left h4 hB0`.

Establish `h6` using `mul_le_mul_of_nonneg_left h3 (norm_nonneg v)`. Establish `h7 : 0 ≤ ‖v‖ * ‖y - z‖` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem low {y : Lie E a} (hy : y ∈ invSet E a) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ z ∈ Metric.ball y r, ∀ v : Fin a → Cinf E, ‖v‖ ≤ M * ‖v ᵥ* Matrix.of z‖ := by
  obtain ⟨u, hu⟩ := hy
  set B : ℝ := a * ‖toL (u⁻¹).val‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
  have hp : 0 < 2 * (B * a + 1) := by positivity
  refine ⟨1 / (2 * (B * a + 1)), 2 * B, by positivity, by positivity, fun z hz v => ?_⟩
  have h1 : ‖v‖ ≤ B * ‖v ᵥ* Matrix.of y‖ := by
    have h := vm_le (v ᵥ* Matrix.of y) (toL (u⁻¹).val)
    have e : (v ᵥ* Matrix.of y) ᵥ* Matrix.of (toL (u⁻¹).val) = v := by
      rw [Matrix.vecMul_vecMul, ← hu]
      change v ᵥ* (u.val * (u⁻¹).val) = v
      rw [Units.mul_inv, Matrix.vecMul_one]
    rw [e] at h
    calc _ ≤ _ := h
      _ = _ := by rw [hB]; ring
  have h2 : v ᵥ* Matrix.of y = v ᵥ* Matrix.of z + v ᵥ* Matrix.of (y - z) := by
    have := (vmL v).map_add z (y - z)
    rw [add_sub_cancel] at this
    exact this
  have h3 : ‖y - z‖ * (2 * (B * a + 1)) ≤ 1 := by
    rw [Metric.mem_ball, dist_comm, dist_eq_norm, lt_div_iff₀ hp] at hz
    exact hz.le
  have h4 : ‖v ᵥ* Matrix.of y‖ ≤ ‖v ᵥ* Matrix.of z‖ + a * ‖v‖ * ‖y - z‖ := by
    rw [h2]
    exact (norm_add_le _ _).trans (by gcongr; exact vm_le v _)
  have h5 := mul_le_mul_of_nonneg_left h4 hB0
  have h6 := mul_le_mul_of_nonneg_left h3 (norm_nonneg v)
  have h7 : 0 ≤ ‖v‖ * ‖y - z‖ := by positivity
  nlinarith

/- English proof (translation)
Use `⟨k.factorial * Real.exp 1, by positivity, fun t ht => ?_⟩` and prove the remaining obligations. Establish `h` using `Real.pow_div_factorial_le_exp (1 + t) (by positivity) k`. Rewrite `h` using `[div_le_iff₀ (by positivity)]`. Establish `h2 : Real.exp (1 + t) * Real.exp (-Real.pi * t) ≤ Real.exp 1 * Real.exp (-Real.pi * (t / 2))`. Rewrite using `[← Real.exp_add, ← Real.exp_add]`.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use polynomial arithmetic with `[Real.pi_gt_three]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem expb (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
    (1 + t) ^ k * Real.exp (-Real.pi * t) ≤ K * Real.exp (-Real.pi * (t / 2)) := by
  refine ⟨k.factorial * Real.exp 1, by positivity, fun t ht => ?_⟩
  have h := Real.pow_div_factorial_le_exp (1 + t) (by positivity) k
  rw [div_le_iff₀ (by positivity)] at h
  have h2 : Real.exp (1 + t) * Real.exp (-Real.pi * t) ≤ Real.exp 1 * Real.exp (-Real.pi * (t / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three]
  calc _ ≤ (Real.exp (1 + t) * k.factorial) * Real.exp (-Real.pi * t) := by gcongr
    _ = k.factorial * (Real.exp (1 + t) * Real.exp (-Real.pi * t)) := by ring
    _ ≤ k.factorial * (Real.exp 1 * Real.exp (-Real.pi * (t / 2))) := by gcongr
    _ = _ := by ring

/- English proof (translation)
Take `⟨r, M, hr, hM, h⟩` from `low hy`. Establish `hq` using `(UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.2.2`. Use `set D : ℝ := a * Fintype.card (InfinitePlace E) with hD`. Establish `hD0 : 0 ≤ D` using `by positivity`. Establish `hp : 0 < 2 * (D * M ^ 2 + 1)` using `by positivity`.

Use `⟨r, M, 1 / (2 * (D * M ^ 2 + 1)), hr, hM, by positivity, fun k => ?_⟩` and prove the remaining obligations. Take `⟨K, hK, hk⟩` from `expb k`. Use `⟨K, fun z hz v => ?_⟩` and prove the remaining obligations. Establish `h1` using `h z hz v`. Establish `h2` using `(hq (v ᵥ* Matrix.of z)).1`.

Establish `h3` using `(hq v).2`. Establish `h0` using `qf_nonneg (v ᵥ* Matrix.of z)`. Use `⟨h1.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖v ᵥ* Matrix.of z‖ - 1)]) hM), ?_⟩` and prove the remaining obligations. Use `(hk _ h0).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK)` and prove the remaining obligations. Establish `h4 : ‖v‖ ^ 2 ≤ M ^ 2 * qf (v ᵥ* Matrix.of z)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h5 : 1 / (2 * (D * M ^ 2 + 1)) * qf v ≤ qf (v ᵥ* Matrix.of z) / 2`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ hp]`. Use `mul_le_mul_of_nonneg_left h4 hD0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Use `mul_le_mul_of_nonneg_left h5 Real.pi_pos.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem dom {y : Lie E a} (hy : y ∈ invSet E a) :
    ∃ r M c : ℝ, 0 < r ∧ 0 ≤ M ∧ 0 < c ∧ ∀ k : ℕ, ∃ K : ℝ, ∀ z ∈ Metric.ball y r, ∀ v : Fin a → Cinf E,
      ‖v‖ ≤ M * (1 + qf (v ᵥ* Matrix.of z)) ∧
      (1 + qf (v ᵥ* Matrix.of z)) ^ k * gauss (v ᵥ* Matrix.of z) ≤ K * Real.exp (-Real.pi * (c * qf v)) := by
  obtain ⟨r, M, hr, hM, h⟩ := low hy
  have hq := (UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.2.2
  set D : ℝ := a * Fintype.card (InfinitePlace E) with hD
  have hD0 : 0 ≤ D := by positivity
  have hp : 0 < 2 * (D * M ^ 2 + 1) := by positivity
  refine ⟨r, M, 1 / (2 * (D * M ^ 2 + 1)), hr, hM, by positivity, fun k => ?_⟩
  obtain ⟨K, hK, hk⟩ := expb k
  refine ⟨K, fun z hz v => ?_⟩
  have h1 := h z hz v
  have h2 := (hq (v ᵥ* Matrix.of z)).1
  have h3 := (hq v).2
  have h0 := qf_nonneg (v ᵥ* Matrix.of z)
  refine ⟨h1.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖v ᵥ* Matrix.of z‖ - 1)]) hM), ?_⟩
  refine (hk _ h0).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK)
  have h4 : ‖v‖ ^ 2 ≤ M ^ 2 * qf (v ᵥ* Matrix.of z) := by
    calc _ ≤ (M * ‖v ᵥ* Matrix.of z‖) ^ 2 := by gcongr
      _ = M ^ 2 * ‖v ᵥ* Matrix.of z‖ ^ 2 := by ring
      _ ≤ _ := by gcongr
  have h5 : 1 / (2 * (D * M ^ 2 + 1)) * qf v ≤ qf (v ᵥ* Matrix.of z) / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    have := mul_le_mul_of_nonneg_left h4 hD0
    nlinarith
  have := mul_le_mul_of_nonneg_left h5 Real.pi_pos.le
  linarith

end

/- English proof (translation)
Introduce `E _ _ a ι x N hS P hP y hy`. Take `⟨r, M, c, hr, hM, hc, hd⟩` from `dom hy`. Take `⟨-, ⟨C, k, hC⟩, -⟩` from `UpperTheory.admissibleFunctionClass_closure_properties E a P hP`. Take `⟨hsm, ⟨C', k', hC'⟩, -⟩` from `UpperTheory.quadratic_form_gradient_formula E a P hP`. Establish `hs` using `(hS.2 c c hc le_rfl).1`.

Establish `hy0 : y ∈ Metric.ball y r` using `Metric.mem_ball_self hr`. Establish `hg : ∀ v : Fin a → Cinf E, 0 < gauss v` using `fun v => Real.exp_pos _`. Establish `h0 : Summable fun i => pg P (x i ᵥ* Matrix.of y)`. Take `⟨K, hK⟩` from `hd k`. Use `Summable.of_norm_bounded (hs.mul_left (|C| * K)) fun i => ?_` and prove the remaining obligations.

Establish `h1` using `(hK y hy0 (x i)).2`. Establish `h2` using `qf_nonneg (x i ᵥ* Matrix.of y)`. Establish `h3` using `hg (x i ᵥ* Matrix.of y)`. Rewrite using `[pg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h3]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(hC _).trans (by gcongr; exact le_abs_self C)`. Use `_ = |C| * ((1 + qf (x i ᵥ* Matrix.of y)) ^ k * gauss (x i ᵥ* Matrix.of y)) := by ring`. Use `_ ≤ |C| * (K * _) := by gcongr`. Use `_ = _ := by ring`. Take `⟨K, hK⟩` from `hd (k' + 1)`.

Establish `hu` using `hs.mul_left (|C'| * (a * M) * K)`. Establish `hb : ∀ i z, z ∈ Metric.ball y r → ‖(fderiv ℝ (pg P) (x i ᵥ* Matrix.of z)).comp (vmL (x i))‖ ≤ |C'| * (a * M) * K * Real.exp (-Real.pi * (c * qf (x i)))`. Introduce `i z hz`. Take `⟨h1, h2⟩` from `hK z hz (x i)`. Establish `h3` using `qf_nonneg (x i ᵥ* Matrix.of z)`.

Establish `h4` using `hg (x i ᵥ* Matrix.of z)`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul ((hC' _).trans (by gcongr; exact le_abs_self C')) ((vmL_norm _).trans (by gcongr)) (norm_nonneg _) (by positivity)` and prove the remaining obligations. Use `_ = |C'| * (a * M) * ((1 + qf (x i ᵥ* Matrix.of z)) ^ (k' + 1) * gauss (x i ᵥ* Matrix.of z)) := by ring`. Use `_ ≤ |C'| * (a * M) * (K * _) := by gcongr`.

Use `_ = _ := by ring`. Establish `hF` using `hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (f := fun i (z : Lie E a) => pg P (x i ᵥ* Matrix.of z)) (f' := fun i z => (fderiv ℝ (pg P) (x i ᵥ* Matrix.of z)).comp (vmL (x i))) hu Metric.isOpen_ball (convex_ball y r).isPreconnected (fun i z _ => ((hsm.differentiable (by simp)) _).h …`. Establish `hF' : HasFDerivAt (msum x P) _ y` using `hF`. Use `⟨h0, hF'.differentiableAt, fun Z => ?_⟩` and prove the remaining obligations. Rewrite using `[hF'.fderiv]`.

Conclude with `(ContinuousLinearMap.apply ℝ ℂ Z).map_tsum (Summable.of_norm_bounded hu fun i => hb i y hy0)`.
-/
theorem UpperTheory.sum_der :
    SumDer := by
  intro E _ _ a ι x N hS P hP y hy
  obtain ⟨r, M, c, hr, hM, hc, hd⟩ := dom hy
  obtain ⟨-, ⟨C, k, hC⟩, -⟩ := UpperTheory.admissibleFunctionClass_closure_properties E a P hP
  obtain ⟨hsm, ⟨C', k', hC'⟩, -⟩ := UpperTheory.quadratic_form_gradient_formula E a P hP
  have hs := (hS.2 c c hc le_rfl).1
  have hy0 : y ∈ Metric.ball y r := Metric.mem_ball_self hr
  have hg : ∀ v : Fin a → Cinf E, 0 < gauss v := fun v => Real.exp_pos _
  have h0 : Summable fun i => pg P (x i ᵥ* Matrix.of y) := by
    obtain ⟨K, hK⟩ := hd k
    refine Summable.of_norm_bounded (hs.mul_left (|C| * K)) fun i => ?_
    have h1 := (hK y hy0 (x i)).2
    have h2 := qf_nonneg (x i ᵥ* Matrix.of y)
    have h3 := hg (x i ᵥ* Matrix.of y)
    rw [pg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h3]
    calc _ ≤ (|C| * (1 + qf (x i ᵥ* Matrix.of y)) ^ k) * gauss (x i ᵥ* Matrix.of y) := by
          gcongr
          exact (hC _).trans (by gcongr; exact le_abs_self C)
      _ = |C| * ((1 + qf (x i ᵥ* Matrix.of y)) ^ k * gauss (x i ᵥ* Matrix.of y)) := by ring
      _ ≤ |C| * (K * _) := by gcongr
      _ = _ := by ring
  obtain ⟨K, hK⟩ := hd (k' + 1)
  have hu := hs.mul_left (|C'| * (a * M) * K)
  have hb : ∀ i z, z ∈ Metric.ball y r → ‖(fderiv ℝ (pg P) (x i ᵥ* Matrix.of z)).comp (vmL (x i))‖ ≤
      |C'| * (a * M) * K * Real.exp (-Real.pi * (c * qf (x i))) := by
    intro i z hz
    obtain ⟨h1, h2⟩ := hK z hz (x i)
    have h3 := qf_nonneg (x i ᵥ* Matrix.of z)
    have h4 := hg (x i ᵥ* Matrix.of z)
    calc _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (|C'| * (1 + qf (x i ᵥ* Matrix.of z)) ^ k' * gauss (x i ᵥ* Matrix.of z)) *
            (a * (M * (1 + qf (x i ᵥ* Matrix.of z)))) := by
          refine mul_le_mul ((hC' _).trans (by gcongr; exact le_abs_self C'))
            ((vmL_norm _).trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = |C'| * (a * M) * ((1 + qf (x i ᵥ* Matrix.of z)) ^ (k' + 1) * gauss (x i ᵥ* Matrix.of z)) := by ring
      _ ≤ |C'| * (a * M) * (K * _) := by gcongr
      _ = _ := by ring
  have hF := hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℝ)
    (f := fun i (z : Lie E a) => pg P (x i ᵥ* Matrix.of z))
    (f' := fun i z => (fderiv ℝ (pg P) (x i ᵥ* Matrix.of z)).comp (vmL (x i)))
    hu Metric.isOpen_ball (convex_ball y r).isPreconnected
    (fun i z _ => ((hsm.differentiable (by simp)) _).hasFDerivAt.comp z (vmL (x i)).hasFDerivAt)
    hb hy0 h0 hy0
  have hF' : HasFDerivAt (msum x P) _ y := hF
  refine ⟨h0, hF'.differentiableAt, fun Z => ?_⟩
  rw [hF'.fderiv]
  exact (ContinuousLinearMap.apply ℝ ℂ Z).map_tsum (Summable.of_norm_bounded hu fun i => hb i y hy0)
