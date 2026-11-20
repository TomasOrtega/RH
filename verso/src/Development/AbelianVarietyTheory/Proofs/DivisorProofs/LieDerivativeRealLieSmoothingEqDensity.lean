import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `set L := lmul X with hL`. Set `b` to `Module.finBasis ℝ (Lie E a)`. Set `c : Fin (Module.finrank ℝ (Lie E a)) → Lie E a → ℂ` to `fun i x => α x * (b.repr (L x) i : ℝ)`. Establish `hc : ∀ i, IsTest (invSet E a) (c i)` using `fun i => hα.mul (Complex.ofRealCLM.contDiff.comp ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp L.contDiff))`. Establish `hG' : ∀ v, ContinuousOn (fun x => fderiv ℝ G x v) (invSet E a)` using `fun v => (hG.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply continuousOn_const`.

Establish `e : ∀ x, α x * fderiv ℝ G x (L x) = ∑ i, c i x * fderiv ℝ G x (b i)` using `fun x => by conv_lhs => rw [← b.sum_repr (L x)]`. Simplify using `only [map_sum, map_smul, Finset.mul_sum, c, Complex.real_smul, mul_assoc]`. Establish `hdc : ∀ i x, fderiv ℝ (c i) x (b i) = α x * (b.repr (L (b i)) i : ℝ) + (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i)`. Introduce `i x`. Establish `h1 : HasFDerivAt (fun x => ((b.repr (L x) i : ℝ) : ℂ)) (Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) x` using `(Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)).hasFDerivAt`.

Establish `h2` using `((hα.1.differentiable (by simp) x).hasFDerivAt).mul h1`. Rewrite using `[show c i = (α * fun x => ((b.repr (L x) i : ℝ) : ℂ)) from rfl, h2.fderiv]`. Simplify using `[Module.Basis.coord_apply, smul_eq_mul]`. Establish `key : ∀ x, ∑ i, fderiv ℝ (c i) x (b i) = -dens X α x`. Introduce `x`.

Establish `h3 : fderiv ℝ α x (L x) = ∑ i, (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i)`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : (LinearMap.trace ℝ (Lie E a) L.toLinearMap : ℂ) = ∑ i, ((b.repr (L (b i)) i : ℝ) : ℂ)`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]`. Simplify using `[LinearMap.toMatrix_apply]`.

Simplify using `only [hdc, Finset.sum_add_distrib, dens, neg_neg, ← hL, h3, h4, Finset.sum_mul]`. Rewrite using `[add_comm]`. Apply the tactic sequence `congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring`. Establish `hi1 : ∀ i, Integrable (fun x => c i x * fderiv ℝ G x (b i)) ν` using `fun i => (hc i).integrable_mul ν isOpen_invSet (hG' _)`. Establish `hi2 : ∀ i, Integrable (fun x => fderiv ℝ (c i) x (b i) * G x) ν` using `fun i => by`.

Simplify using `using (((hc i).fderiv (b i)).mul contDiff_const (β := fun _ => (1 : ℂ))).integrable_mul ν isOpen_invSet hG.continuousOn`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi2 i) (hi1 i) ((hc i).integrable_mul ν isOpen_invSet hG.continuousOn) (fun x _ => (hc i).1.differentiable (by simp) x) (fun x hx => (hG.contDiffAt (isOpen_invSet.mem_nhds ((hc i).2.2 hx))).differentiableAt (by simp)), integra …`. Use `_ = ∫ x, ∑ i, -(fderiv ℝ (c i) x (b i) * G x) ∂ν := (integral_finset_sum _ fun i _ => (hi2 i).neg).symm`.

Use `_ = ∫ x, dens X α x * G x ∂ν := by`. Use `integral_congr_ae (.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finset.sum_neg_distrib, ← Finset.sum_mul, key, neg_mul, neg_neg]`.
-/
theorem integral_mul_fderiv_lmul_eq_dens (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) (X : Lie E a) {G : Lie E a → ℂ} (hG : ContDiffOn ℝ ∞ G (invSet E a)) :
    ∫ x, α x * fderiv ℝ G x (lmul X x) ∂ν = ∫ x, dens X α x * G x ∂ν := by
  set L := lmul X with hL
  let b := Module.finBasis ℝ (Lie E a)
  let c : Fin (Module.finrank ℝ (Lie E a)) → Lie E a → ℂ := fun i x => α x * (b.repr (L x) i : ℝ)
  have hc : ∀ i, IsTest (invSet E a) (c i) := fun i => hα.mul (Complex.ofRealCLM.contDiff.comp
    ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp L.contDiff))
  have hG' : ∀ v, ContinuousOn (fun x => fderiv ℝ G x v) (invSet E a) := fun v =>
    (hG.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply continuousOn_const
  have e : ∀ x, α x * fderiv ℝ G x (L x) = ∑ i, c i x * fderiv ℝ G x (b i) := fun x => by
    conv_lhs => rw [← b.sum_repr (L x)]
    simp only [map_sum, map_smul, Finset.mul_sum, c, Complex.real_smul, mul_assoc]
  have hdc : ∀ i x, fderiv ℝ (c i) x (b i) =
      α x * (b.repr (L (b i)) i : ℝ) + (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i) := by
    intro i x
    have h1 : HasFDerivAt (fun x => ((b.repr (L x) i : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) x :=
      (Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)).hasFDerivAt
    have h2 := ((hα.1.differentiable (by simp) x).hasFDerivAt).mul h1
    rw [show c i = (α * fun x => ((b.repr (L x) i : ℝ) : ℂ)) from rfl, h2.fderiv]
    simp [Module.Basis.coord_apply, smul_eq_mul]
  have key : ∀ x, ∑ i, fderiv ℝ (c i) x (b i) = -dens X α x := by
    intro x
    have h3 : fderiv ℝ α x (L x) = ∑ i, (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i) := by
      calc fderiv ℝ α x (L x) = fderiv ℝ α x (∑ i, b.repr (L x) i • b i) := by rw [b.sum_repr]
        _ = _ := by rw [map_sum]; simp only [map_smul, Complex.real_smul]
    have h4 : (LinearMap.trace ℝ (Lie E a) L.toLinearMap : ℂ) = ∑ i, ((b.repr (L (b i)) i : ℝ) : ℂ) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
      simp [LinearMap.toMatrix_apply]
    simp only [hdc, Finset.sum_add_distrib, dens, neg_neg, ← hL, h3, h4, Finset.sum_mul]
    rw [add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have hi1 : ∀ i, Integrable (fun x => c i x * fderiv ℝ G x (b i)) ν := fun i =>
    (hc i).integrable_mul ν isOpen_invSet (hG' _)
  have hi2 : ∀ i, Integrable (fun x => fderiv ℝ (c i) x (b i) * G x) ν := fun i => by
    simpa using (((hc i).fderiv (b i)).mul contDiff_const (β := fun _ => (1 : ℂ))).integrable_mul ν isOpen_invSet
      hG.continuousOn
  calc ∫ x, α x * fderiv ℝ G x (L x) ∂ν = ∫ x, ∑ i, c i x * fderiv ℝ G x (b i) ∂ν := integral_congr_ae (.of_forall e)
    _ = ∑ i, ∫ x, c i x * fderiv ℝ G x (b i) ∂ν := integral_finset_sum _ fun i _ => hi1 i
    _ = ∑ i, ∫ x, -(fderiv ℝ (c i) x (b i) * G x) ∂ν := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi2 i) (hi1 i)
        ((hc i).integrable_mul ν isOpen_invSet hG.continuousOn)
        (fun x _ => (hc i).1.differentiable (by simp) x)
        (fun x hx => (hG.contDiffAt (isOpen_invSet.mem_nhds ((hc i).2.2 hx))).differentiableAt (by simp)),
        integral_neg]
    _ = ∫ x, ∑ i, -(fderiv ℝ (c i) x (b i) * G x) ∂ν := (integral_finset_sum _ fun i _ => (hi2 i).neg).symm
    _ = ∫ x, dens X α x * G x ∂ν := by
      refine integral_congr_ae (.of_forall fun x => ?_)
      dsimp only
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, key, neg_mul, neg_neg]

namespace SmoothingDeriv

omit [IsTotallyComplex E] in

/- English proof (translation)
Set `R : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a)` to `{ toFun := rmul map_add' := fun x y => ContinuousLinearMap.ext fun z => show Matrix.of z * Matrix.of (x + y) = Matrix.of z * Matrix.of x + Matrix.of z * Matrix.of y by`. Rewrite using `[← Matrix.of_add_of, Matrix.mul_add]`. Use the proof step `map_smul' := fun c x => ContinuousLinearMap.ext fun z => show Matrix.of z * Matrix.of (c • x) = c • (Matrix.of z * Matrix.of x) by`. Rewrite using `[← Matrix.smul_of, Matrix.mul_smul] }`. Conclude with `R.continuous_of_finiteDimensional`.
-/
theorem continuous_rmul_fun : Continuous (fun y : Lie E a => rmul y) := by
  let R : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) :=
    { toFun := rmul
      map_add' := fun x y => ContinuousLinearMap.ext fun z =>
        show Matrix.of z * Matrix.of (x + y) = Matrix.of z * Matrix.of x + Matrix.of z * Matrix.of y by
          rw [← Matrix.of_add_of, Matrix.mul_add]
      map_smul' := fun c x => ContinuousLinearMap.ext fun z =>
        show Matrix.of z * Matrix.of (c • x) = c • (Matrix.of z * Matrix.of x) by
          rw [← Matrix.smul_of, Matrix.mul_smul] }
  exact R.continuous_of_finiteDimensional

omit [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `one_mul (Matrix.of y)`.
-/
theorem lmul_oneL (y : Lie E a) : lmul (oneL E a) y = y := one_mul (Matrix.of y)

omit [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `Continuous.matrix_mul (A := fun p : Lie E a × Lie E a => Matrix.of p.1) (B := fun p : Lie E a × Lie E a => Matrix.of p.2) continuous_fst continuous_snd`.
-/
theorem continuous_lmul_pair : Continuous fun p : Lie E a × Lie E a => lmul p.1 p.2 :=
  Continuous.matrix_mul (A := fun p : Lie E a × Lie E a => Matrix.of p.1) (B := fun p : Lie E a × Lie E a => Matrix.of p.2)
    continuous_fst continuous_snd

/- English proof (translation)
Use function extensionality and compare the values at `z`. Distinguish the cases in `h : IsUnit (Matrix.of z)`. Take `⟨u, hu⟩` from `h`. Take `rfl : z = toL u.val` from `hu.symm`. Rewrite using `[chart_val, smoothing, chart_mul]`.

Both sides reduce to the same expression. Establish `h' : ∀ y, chart ψ g (lmul z y) = 0` using `fun y => by`. Establish `hn : ¬ IsUnit (Matrix.of (lmul z y))` using `fun hy => h (by`. Establish `h2` using `(Matrix.isUnit_iff_isUnit_det _).1 hy`. Express the relevant statement in the definitionally equal form `IsUnit (Matrix.of z * Matrix.of y).det at h2`.

Rewrite `h2` using `[Matrix.det_mul]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left h2))`. Simplify using `[chart, hn]`. Simplify using `only [h', mul_zero, integral_zero]`. Simplify using `[chart, h]`.
-/
theorem chart_smoothing (ν : Measure (Lie E a)) (α : Lie E a → ℂ) (ψ : GA E a → ℂ) (g : GA E a) :
    chart (smoothing ν α ψ) g = fun z => ∫ y, α y * chart ψ g (lmul z y) ∂ν := by
  funext z
  by_cases h : IsUnit (Matrix.of z)
  · obtain ⟨u, hu⟩ := h
    obtain rfl : z = toL u.val := hu.symm
    rw [chart_val, smoothing, chart_mul]
    rfl
  · have h' : ∀ y, chart ψ g (lmul z y) = 0 := fun y => by
      have hn : ¬ IsUnit (Matrix.of (lmul z y)) := fun hy => h (by
        have h2 := (Matrix.isUnit_iff_isUnit_det _).1 hy
        change IsUnit (Matrix.of z * Matrix.of y).det at h2
        rw [Matrix.det_mul] at h2
        exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left h2))
      simp [chart, hn]
    simp only [h', mul_zero, integral_zero]
    simp [chart, h]

end SmoothingDeriv

open SmoothingDeriv in

/- English proof (translation)
Use `set f := chart ψ g with hf`. Establish `hfs : ContDiffOn ℝ ∞ f (invSet E a)` using `hψ g`. Establish `hfd : ContinuousOn (fderiv ℝ f) (invSet E a)` using `hfs.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)`. Establish `hmul : ∀ z y, z ∈ invSet E a → y ∈ invSet E a → lmul z y ∈ invSet E a` using `fun z y hz hy => IsUnit.mul hz hy`. Take `⟨ε, ε0, hε⟩` from `Metric.isOpen_iff.1 isOpen_invSet (oneL E a) isUnit_one`.

Establish `hr : 0 < ε / 2` using `half_pos ε0`. Establish `hball : Metric.closedBall (oneL E a) (ε / 2) ⊆ invSet E a` using `(Metric.closedBall_subset_ball (half_lt_self ε0)).trans hε`. Use `set K := (fun p : Lie E a × Lie E a => lmul p.1 p.2) '' (Metric.closedBall (oneL E a) (ε / 2) ×ˢ tsupport α)`. Establish `hKc : IsCompact K` using `((isCompact_closedBall _ _).prod hα.2.1.isCompact).image continuous_lmul_pair`. Establish `hKs : K ⊆ invSet E a`.

Introduce and unpack `_ ⟨p, ⟨hp1, hp2⟩, rfl⟩`. Conclude with `hmul _ _ (hball hp1) (hα.2.2 hp2)`. Take `⟨C, hC⟩` from `hKc.exists_bound_of_continuousOn (hfd.mono hKs)`. Set `F : Lie E a → Lie E a → ℂ` to `fun z y => α y * f (lmul z y)`. Set `F' : Lie E a → Lie E a → (Lie E a →L[ℝ] ℂ)` to `fun z y => α y • (fderiv ℝ f (lmul z y)).comp (rmul y)`.

Establish `hcontOn : ∀ z ∈ invSet E a, ContinuousOn (fun y => f (lmul z y)) (invSet E a)` using `fun z hz => hfs.continuousOn.comp (lmul z).continuous.continuousOn fun y hy => hmul z y hz hy`. Establish `hF'c : Continuous (F' (oneL E a))`. Use `continuous_of_tsupport fun y hy => ?_` and prove the remaining obligations. Establish `hy' : y ∈ invSet E a` using `hα.2.2 (tsupport_smul_subset_left _ _ hy)`. Simplify using `only [F', lmul_oneL]`.

Conclude with `hα.1.continuous.continuousAt.smul ((hfd.continuousAt (isOpen_invSet.mem_nhds hy')).clm_comp continuous_rmul_fun.continuousAt)`. Establish `hbound : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), ‖F' z y‖ ≤ ‖α y‖ * (C * ‖rmul y‖)`. Introduce `y z hz`. Distinguish the cases in `h0 : α y = 0`. Simplify using `[F', h0]`.

Establish `hy : y ∈ tsupport α` using `subset_tsupport _ h0`. Establish `hK : lmul z y ∈ K` using `⟨(z, y), ⟨Metric.ball_subset_closedBall hz, hy⟩, rfl⟩`. Rewrite using `[norm_smul]`. Conclude with `mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hC _ hK) (norm_nonneg _))) (norm_nonneg _)`. Establish `hbi : Integrable (fun y => ‖α y‖ * (C * ‖rmul y‖)) ν` using `(hα.1.continuous.norm.mul (continuous_const.mul continuous_rmul_fun.norm)).integrable_of_hasCompactSupport hα.2.1.norm.mul_right`.

Establish `hdiff : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), HasFDerivAt (fun z => F z y) (F' z y) z`. Introduce `y z hz`. Distinguish the cases in `h0 : α y = 0`. Simplify using `only [F, F', h0, zero_mul, zero_smul]`. Conclude with `hasFDerivAt_const 0 z`.

Establish `hy : y ∈ invSet E a` using `hα.2.2 (subset_tsupport _ h0)`. Establish `hw : lmul z y ∈ invSet E a` using `hmul _ _ (hball (Metric.ball_subset_closedBall hz)) hy`. Establish `h1 : HasFDerivAt f (fderiv ℝ f (lmul z y)) (rmul y z)` using `((hfs.contDiffAt (isOpen_invSet.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt`. Conclude with `(h1.comp z (rmul y).hasFDerivAt).const_mul (α y)`. Establish `hmain` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := F) (F' := F') (Metric.ball_mem_nhds _ hr) (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) fun z hz => (hα.continuous_mul isOpen_invSet (hcontOn z (hball (Metric.ball_subset_closedBall hz)))).aestronglyMeasurable) …`.

Establish `hint : Integrable (F' (oneL E a)) ν` using `hbi.mono' hF'c.aestronglyMeasurable (.of_forall fun y => hbound y _ (Metric.mem_ball_self hr))`. Rewrite using `[lieD, chart_smoothing, ← hf, hmain.fderiv, ContinuousLinearMap.integral_apply hint, smoothing, ← integral_mul_fderiv_lmul_eq_dens ν hα X hfs]`. Use `integral_congr_ae (.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [F', lmul_oneL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem lieD_smoothing (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) {ψ : GA E a → ℂ} (hψ : ψ ∈ Sm E a) (X : Lie E a) (g : GA E a) :
    lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g := by
  set f := chart ψ g with hf
  have hfs : ContDiffOn ℝ ∞ f (invSet E a) := hψ g
  have hfd : ContinuousOn (fderiv ℝ f) (invSet E a) :=
    hfs.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
  have hmul : ∀ z y, z ∈ invSet E a → y ∈ invSet E a → lmul z y ∈ invSet E a :=
    fun z y hz hy => IsUnit.mul hz hy
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.1 isOpen_invSet (oneL E a) isUnit_one
  have hr : 0 < ε / 2 := half_pos ε0
  have hball : Metric.closedBall (oneL E a) (ε / 2) ⊆ invSet E a :=
    (Metric.closedBall_subset_ball (half_lt_self ε0)).trans hε
  set K := (fun p : Lie E a × Lie E a => lmul p.1 p.2) '' (Metric.closedBall (oneL E a) (ε / 2) ×ˢ tsupport α)
  have hKc : IsCompact K := ((isCompact_closedBall _ _).prod hα.2.1.isCompact).image continuous_lmul_pair
  have hKs : K ⊆ invSet E a := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact hmul _ _ (hball hp1) (hα.2.2 hp2)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hfd.mono hKs)
  let F : Lie E a → Lie E a → ℂ := fun z y => α y * f (lmul z y)
  let F' : Lie E a → Lie E a → (Lie E a →L[ℝ] ℂ) := fun z y => α y • (fderiv ℝ f (lmul z y)).comp (rmul y)
  have hcontOn : ∀ z ∈ invSet E a, ContinuousOn (fun y => f (lmul z y)) (invSet E a) := fun z hz =>
    hfs.continuousOn.comp (lmul z).continuous.continuousOn fun y hy => hmul z y hz hy
  have hF'c : Continuous (F' (oneL E a)) := by
    refine continuous_of_tsupport fun y hy => ?_
    have hy' : y ∈ invSet E a := hα.2.2 (tsupport_smul_subset_left _ _ hy)
    simp only [F', lmul_oneL]
    exact hα.1.continuous.continuousAt.smul
      ((hfd.continuousAt (isOpen_invSet.mem_nhds hy')).clm_comp continuous_rmul_fun.continuousAt)
  have hbound : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), ‖F' z y‖ ≤ ‖α y‖ * (C * ‖rmul y‖) := by
    intro y z hz
    by_cases h0 : α y = 0
    · simp [F', h0]
    have hy : y ∈ tsupport α := subset_tsupport _ h0
    have hK : lmul z y ∈ K := ⟨(z, y), ⟨Metric.ball_subset_closedBall hz, hy⟩, rfl⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC _ hK) (norm_nonneg _))) (norm_nonneg _)
  have hbi : Integrable (fun y => ‖α y‖ * (C * ‖rmul y‖)) ν :=
    (hα.1.continuous.norm.mul (continuous_const.mul continuous_rmul_fun.norm)).integrable_of_hasCompactSupport
      hα.2.1.norm.mul_right
  have hdiff : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), HasFDerivAt (fun z => F z y) (F' z y) z := by
    intro y z hz
    by_cases h0 : α y = 0
    · simp only [F, F', h0, zero_mul, zero_smul]; exact hasFDerivAt_const 0 z
    have hy : y ∈ invSet E a := hα.2.2 (subset_tsupport _ h0)
    have hw : lmul z y ∈ invSet E a := hmul _ _ (hball (Metric.ball_subset_closedBall hz)) hy
    have h1 : HasFDerivAt f (fderiv ℝ f (lmul z y)) (rmul y z) :=
      ((hfs.contDiffAt (isOpen_invSet.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp z (rmul y).hasFDerivAt).const_mul (α y)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := F) (F' := F') (Metric.ball_mem_nhds _ hr)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) fun z hz =>
      (hα.continuous_mul isOpen_invSet (hcontOn z (hball (Metric.ball_subset_closedBall hz)))).aestronglyMeasurable)
    (hα.integrable_mul ν isOpen_invSet (hcontOn _ isUnit_one)) hF'c.aestronglyMeasurable
    (.of_forall hbound) hbi (.of_forall hdiff)
  have hint : Integrable (F' (oneL E a)) ν :=
    hbi.mono' hF'c.aestronglyMeasurable (.of_forall fun y => hbound y _ (Metric.mem_ball_self hr))
  rw [lieD, chart_smoothing, ← hf, hmain.fderiv, ContinuousLinearMap.integral_apply hint, smoothing,
    ← integral_mul_fderiv_lmul_eq_dens ν hα X hfs]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [F', lmul_oneL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rfl

/- English proof (translation)
Introduce `_ _ _ _ _ ν _ _ hα _ hψ X g` and use `lieD_smoothing ν hα hψ X g`.
-/
theorem lieD_smoothing_eq_dens : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a,
    ∀ (X : Lie E a) (g : GA E a), lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g :=
  fun _ _ _ _ _ ν _ _ hα _ hψ X g => lieD_smoothing ν hα hψ X g

end GlobalTheory.AutGrowth

end
