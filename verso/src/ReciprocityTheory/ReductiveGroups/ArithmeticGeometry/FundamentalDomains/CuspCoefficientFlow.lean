import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds

namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology

noncomputable section

section Param

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC x0 (mem_ball_self hρ))`. Establish `hx1 : ‖x - x0‖ < ρ / 2` using `mem_ball_iff_norm.mp hx`. Establish `hxd : DifferentiableAt ℂ f x` using `hf.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hx))`. Use `ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_` and prove the remaining obligations. Break down `eq_or_ne v 0 with rfl | hv` into its components or cases.

Simplify using the standard rewrite rules. Establish `hvpos : 0 < ‖v‖` using `norm_pos_iff.mpr hv`. Use `set R := ρ / 2 / ‖v‖ with hRdef`. Establish `hR : 0 < R` using `by positivity`. Establish `hRv : R * ‖v‖ = ρ / 2` using `div_mul_cancel₀ _ hvpos.ne'`.

Establish `hmem : ∀ w : ℂ, ‖w‖ ≤ R → x + w • v ∈ ball x0 ρ`. Introduce `w hw`. Rewrite using `[mem_ball_iff_norm]`. Establish `h2 : ‖w • v‖ ≤ ρ / 2`. Rewrite using `[norm_smul, ← hRv]`.

Conclude with `mul_le_mul_of_nonneg_right hw (norm_nonneg v)`. Establish `h3 : x + w • v - x0 = (x - x0) + w • v` using `by abel`. Rewrite using `[h3]`. Combine the equalities or inequalities in the displayed calculation. Establish `hgd : DifferentiableOn ℂ (fun w : ℂ => f (x + w • v)) (closedBall 0 R)`.

Introduce `w hw`. Establish `hw' : ‖w‖ ≤ R` using `by simpa using hw`. Establish `hfa : DifferentiableAt ℂ f (x + w • v)` using `hf.differentiableAt (isOpen_ball.mem_nhds (hmem w hw'))`. Conclude with `(hfa.comp w ((differentiableAt_id.smul_const v).const_add x)).differentiableWithinAt`. Establish `hdc : DiffContOnCl ℂ (fun w : ℂ => f (x + w • v)) (ball 0 R)`.

Apply `DifferentiableOn.diffContOnCl` to reduce the goal to its premises. Rewrite using `[closure_ball _ hR.ne']`. Conclude with `hgd`. Establish `hcau` using `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc (fun z hz => hC _ (hmem z (le_of_eq (mem_sphere_zero_iff_norm.mp hz))))`. Establish `hline : HasDerivAt (fun w : ℂ => x + w • v) ((1 : ℂ) • v) 0` using `((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x`.

Establish `hfd : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v)`. Rewrite using `[zero_smul, add_zero]`. Conclude with `hxd.hasFDerivAt`. Establish `hg` using `hfd.comp_hasDerivAt (0 : ℂ) hline`. Rewrite `hg` using `[one_smul]`.

Establish `hder : deriv (fun w : ℂ => f (x + w • v)) 0 = fderiv ℂ f x v` using `hg.deriv`. Rewrite `hcau` using `[hder]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hRdef]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem norm_fderiv_le_of_differentiableOn_ball_of_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : F → ℂ} {x0 x : F} {ρ C : ℝ} (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (ball x0 ρ))
    (hC : ∀ z ∈ ball x0 ρ, ‖f z‖ ≤ C) (hx : x ∈ ball x0 (ρ / 2)) :
    ‖fderiv ℂ f x‖ ≤ C / (ρ / 2) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x0 (mem_ball_self hρ))
  have hx1 : ‖x - x0‖ < ρ / 2 := mem_ball_iff_norm.mp hx
  have hxd : DifferentiableAt ℂ f x :=
    hf.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hx))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set R := ρ / 2 / ‖v‖ with hRdef
  have hR : 0 < R := by positivity
  have hRv : R * ‖v‖ = ρ / 2 := div_mul_cancel₀ _ hvpos.ne'
  have hmem : ∀ w : ℂ, ‖w‖ ≤ R → x + w • v ∈ ball x0 ρ := by
    intro w hw
    rw [mem_ball_iff_norm]
    have h2 : ‖w • v‖ ≤ ρ / 2 := by
      rw [norm_smul, ← hRv]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg v)
    have h3 : x + w • v - x0 = (x - x0) + w • v := by abel
    rw [h3]
    calc _ ≤ ‖x - x0‖ + ‖w • v‖ := norm_add_le _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add_of_lt_of_le hx1 h2
      _ = ρ := by ring
  have hgd : DifferentiableOn ℂ (fun w : ℂ => f (x + w • v)) (closedBall 0 R) := by
    intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using hw
    have hfa : DifferentiableAt ℂ f (x + w • v) :=
      hf.differentiableAt (isOpen_ball.mem_nhds (hmem w hw'))
    exact (hfa.comp w ((differentiableAt_id.smul_const v).const_add x)).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun w : ℂ => f (x + w • v)) (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    exact hgd
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc
    (fun z hz => hC _ (hmem z (le_of_eq (mem_sphere_zero_iff_norm.mp hz))))
  have hline : HasDerivAt (fun w : ℂ => x + w • v) ((1 : ℂ) • v) 0 :=
    ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hfd : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
    rw [zero_smul, add_zero]
    exact hxd.hasFDerivAt
  have hg := hfd.comp_hasDerivAt (0 : ℂ) hline
  rw [one_smul] at hg
  have hder : deriv (fun w : ℂ => f (x + w • v)) 0 = fderiv ℂ f x v := hg.deriv
  rw [hder] at hcau
  calc ‖fderiv ℂ f x v‖ ≤ C / R := hcau
    _ = C / (ρ / 2) * ‖v‖ := by
      rw [hRdef]
      field_simp

/- English proof (translation)
Introduce `x0 hx0`. Take `⟨ρ, hρ, C, hsub, hC⟩` from `hbd x0 hx0`. Use `haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hKv.ne`. Establish `hballU : ball x0 ρ ⊆ U` using `ball_subset_closedBall.trans hsub`. Establish `hslice : ∀ t, DifferentiableOn ℂ (fun z => G (A t z)) U` using `fun t => hG.comp (A t).differentiable.differentiableOn (fun z hz => hAU t z hz)`.

Establish `hAx : ∀ x, Continuous fun t => A t x` using `fun x => hA.clm_apply continuous_const`. Establish `hcont : ∀ x ∈ U, Continuous fun t => G (A t x) * e t` using `fun x hx => (hG.continuousOn.comp_continuous (hAx x) (fun t => hAU t x hx)).mul he`. Establish `hfd : ∀ t, ∀ x ∈ U, HasFDerivAt (fun z => G (A t z) * e t) (e t • fderiv ℂ (fun z => G (A t z)) x) x` using `fun t x hx => ((hslice t).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.mul_const (e t)`. Establish `hF'eq : (fun t => e t • fderiv ℂ (fun z => G (A t z)) x0) = fun t => e t • (fderiv ℂ G (A t x0)).comp (A t)`. Use function extensionality and compare the values at `t`.

Use `congr 1`. Establish `hGd : DifferentiableAt ℂ G (A t x0)` using `hG.differentiableAt (hU.mem_nhds (hAU t x0 hx0))`. Conclude with `fderiv_comp x0 hGd (A t).differentiableAt |>.trans (by rw [(A t).fderiv])`. Establish `hmeasF' : AEStronglyMeasurable (fun t => e t • fderiv ℂ (fun z => G (A t z)) x0) (volume.restrict K)`. Rewrite using `[hF'eq]`.

Use `he.aestronglyMeasurable.smul ?_` and prove the remaining obligations. Use `letI : MeasurableSpace (F →L[ℂ] ℂ) := borel _`. Use `haveI : BorelSpace (F →L[ℂ] ℂ) := ⟨rfl⟩`. Establish `hm : Measurable (fderiv ℂ G)` using `measurable_fderiv ℂ G`. Establish `h1 : AEStronglyMeasurable (fun t => fderiv ℂ G (A t x0)) (volume.restrict K)` using `(hm.comp (hAx x0).measurable).aestronglyMeasurable`.

Conclude with `(ContinuousLinearMap.compL ℂ F F ℂ).aestronglyMeasurable_comp₂ h1 hA.aestronglyMeasurable`. Establish `key` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K) (F := fun x t => G (A t x) * e t) (F' := fun x t => e t • fderiv ℂ (fun z => G (A t z)) x) (bound := fun _ => C / (ρ / 2)) (x₀ := x0) (ball_mem_nhds x0 (half_pos hρ)) (Filter.eventually_of_mem (hU.mem_nhds hx …`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `hmeasF'`.

Use the proof step `(Filter.Eventually.of_forall fun t x hx => by`. Rewrite using `[norm_smul]`. Establish `hb` using `norm_fderiv_le_of_differentiableOn_ball_of_norm_le hρ ((hslice t).mono hballU) (fun z hz => hC t z (ball_subset_closedBall hz)) hx`. Establish `hC0 : 0 ≤ C / (ρ / 2)` using `(norm_nonneg _).trans hb`. Combine the equalities or inequalities in the displayed calculation.

Use the proof step `(integrable_const _)`. Use the proof step `(Filter.Eventually.of_forall fun t x hx => hfd t x (hballU (ball_subset_ball (by linarith) hx)))`. Conclude with `key.differentiableAt.differentiableWithinAt`.
-/
theorem diffOn_param_bdd {K : Set (ι → ℝ)} (hKv : volume K < ⊤)
    (A : (ι → ℝ) → F →L[ℂ] F) (hA : Continuous A) {U : Set F} (hU : IsOpen U)
    (hAU : ∀ t, ∀ x ∈ U, A t x ∈ U) (G : F → ℂ) (hG : DifferentiableOn ℂ G U)
    (e : (ι → ℝ) → ℂ) (he : Continuous e) (he1 : ∀ t, ‖e t‖ ≤ 1)
    (hbd : ∀ x0 ∈ U, ∃ ρ > 0, ∃ C, closedBall x0 ρ ⊆ U ∧
      ∀ t, ∀ z ∈ closedBall x0 ρ, ‖G (A t z)‖ ≤ C) :
    DifferentiableOn ℂ (fun x => ∫ t in K, G (A t x) * e t) U := by
  intro x0 hx0
  obtain ⟨ρ, hρ, C, hsub, hC⟩ := hbd x0 hx0
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hKv.ne
  have hballU : ball x0 ρ ⊆ U := ball_subset_closedBall.trans hsub
  have hslice : ∀ t, DifferentiableOn ℂ (fun z => G (A t z)) U := fun t =>
    hG.comp (A t).differentiable.differentiableOn (fun z hz => hAU t z hz)
  have hAx : ∀ x, Continuous fun t => A t x := fun x => hA.clm_apply continuous_const
  have hcont : ∀ x ∈ U, Continuous fun t => G (A t x) * e t := fun x hx =>
    (hG.continuousOn.comp_continuous (hAx x) (fun t => hAU t x hx)).mul he
  have hfd : ∀ t, ∀ x ∈ U, HasFDerivAt (fun z => G (A t z) * e t)
      (e t • fderiv ℂ (fun z => G (A t z)) x) x := fun t x hx =>
    ((hslice t).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.mul_const (e t)
  have hF'eq : (fun t => e t • fderiv ℂ (fun z => G (A t z)) x0) =
      fun t => e t • (fderiv ℂ G (A t x0)).comp (A t) := by
    funext t
    congr 1
    have hGd : DifferentiableAt ℂ G (A t x0) := hG.differentiableAt (hU.mem_nhds (hAU t x0 hx0))
    exact fderiv_comp x0 hGd (A t).differentiableAt |>.trans (by rw [(A t).fderiv])
  have hmeasF' : AEStronglyMeasurable (fun t => e t • fderiv ℂ (fun z => G (A t z)) x0)
      (volume.restrict K) := by
    rw [hF'eq]
    refine he.aestronglyMeasurable.smul ?_
    letI : MeasurableSpace (F →L[ℂ] ℂ) := borel _
    haveI : BorelSpace (F →L[ℂ] ℂ) := ⟨rfl⟩
    have hm : Measurable (fderiv ℂ G) := measurable_fderiv ℂ G
    have h1 : AEStronglyMeasurable (fun t => fderiv ℂ G (A t x0)) (volume.restrict K) :=
      (hm.comp (hAx x0).measurable).aestronglyMeasurable
    exact (ContinuousLinearMap.compL ℂ F F ℂ).aestronglyMeasurable_comp₂ h1 hA.aestronglyMeasurable
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K)
    (F := fun x t => G (A t x) * e t) (F' := fun x t => e t • fderiv ℂ (fun z => G (A t z)) x)
    (bound := fun _ => C / (ρ / 2)) (x₀ := x0) (ball_mem_nhds x0 (half_pos hρ))
    (Filter.eventually_of_mem (hU.mem_nhds hx0) fun x hx => (hcont x hx).aestronglyMeasurable)
    ((integrable_const C).mono' (hcont x0 hx0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        calc ‖G (A t x0)‖ * ‖e t‖ ≤ C * 1 :=
              mul_le_mul (hC t x0 (mem_closedBall_self hρ.le)) (he1 t) (norm_nonneg _)
                ((norm_nonneg _).trans (hC t x0 (mem_closedBall_self hρ.le)))
          _ = C := mul_one C))
    hmeasF'
    (Filter.Eventually.of_forall fun t x hx => by
      rw [norm_smul]
      have hb := norm_fderiv_le_of_differentiableOn_ball_of_norm_le hρ ((hslice t).mono hballU)
        (fun z hz => hC t z (ball_subset_closedBall hz)) hx
      have hC0 : 0 ≤ C / (ρ / 2) := (norm_nonneg _).trans hb
      calc ‖e t‖ * ‖fderiv ℂ (fun z => G (A t z)) x‖ ≤ 1 * (C / (ρ / 2)) :=
            mul_le_mul (he1 t) hb (norm_nonneg _) zero_le_one
        _ = C / (ρ / 2) := one_mul _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun t x hx =>
      hfd t x (hballU (ball_subset_ball (by linarith) hx)))
  exact key.differentiableAt.differentiableWithinAt

end Param

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def flowL (ξ : Fin r → E) (s : X.Ψ → ℝ) : Frame X.Ψ r →L[ℂ] Frame X.Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := X.flow ξ (fun τ => (s τ : ℂ))
      map_add' x y := by
        funext τ
        show X.flowMat ξ τ (s τ : ℂ) * (mat x τ + mat y τ) = _
        rw [Matrix.mul_add]; rfl
      map_smul' c x := by
        funext τ
        show X.flowMat ξ τ (s τ : ℂ) * (c • mat x τ) = _
        rw [Matrix.mul_smul]; rfl }

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma flowL_apply (ξ : Fin r → E) (s : X.Ψ → ℝ) (x : Frame X.Ψ r) :
    flowL X ξ s x = X.flow ξ (fun τ => (s τ : ℂ)) x := rfl

/- English proof (translation)
Apply `continuous_clm_apply.mpr` to reduce the goal to its premises. Introduce `x`. Simplify using `only [flowL_apply]`. Unfold `Data.flow`. Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.mul_apply, Data.flowMat, Matrix.of_apply]`. Use `first`. Consider the case `fun_prop`. Consider the case `continuity`.
-/
lemma cont_flowL (ξ : Fin r → E) : Continuous fun s => flowL X ξ s := by
  apply continuous_clm_apply.mpr
  intro x
  simp only [flowL_apply]
  unfold Data.flow
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.mul_apply, Data.flowMat, Matrix.of_apply]
  first
  | fun_prop
  | continuity

/- English proof (translation)
Unfold `dmin lminor`. Apply `Continuous.matrix_det` to reduce the goal to its premises. Apply `Continuous.matrix_submatrix` to reduce the goal to its premises. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [gram, Matrix.of_apply, hermC, col, mat]`.

Use `first`. Consider the case `fun_prop`. Consider the case `continuity`.
-/
lemma cont_dmin (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  unfold dmin lminor
  apply Continuous.matrix_det
  apply Continuous.matrix_submatrix
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gram, Matrix.of_apply, hermC, col, mat]
  first
  | fun_prop
  | continuity

/- English proof (translation)
Establish `h : ∀ (τ : X.Ψ) (i : Fin r), ContinuousAt (fun x : Frame X.Ψ r => ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) x0`. Introduce `τ i`. Establish `hd1` using `(cont_dmin X τ i.succ).continuousAt (x := x0)`. Establish `hd2` using `(cont_dmin X τ i.castSucc).continuousAt (x := x0)`. Establish `hne1` using `FlowCoefficientBounds.dmin_ne X hx0 τ i.succ`.

Establish `hne2` using `FlowCoefficientBounds.dmin_ne X hx0 τ i.castSucc`. Conclude with `(hd1.div hd2 hne2).norm.rpow_const (Or.inl (norm_ne_zero_iff.mpr (div_ne_zero hne1 hne2)))`. Unfold `Data.nfac`. Conclude with `tendsto_finset_prod _ fun τ _ => tendsto_finset_prod _ fun i _ => h τ i`.
-/
lemma continuousAt_nfac (la : Wt X.Ψ r) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) :
    ContinuousAt (X.nfac la) x0 := by
  have h : ∀ (τ : X.Ψ) (i : Fin r), ContinuousAt (fun x : Frame X.Ψ r =>
      ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) x0 := by
    intro τ i
    have hd1 := (cont_dmin X τ i.succ).continuousAt (x := x0)
    have hd2 := (cont_dmin X τ i.castSucc).continuousAt (x := x0)
    have hne1 := FlowCoefficientBounds.dmin_ne X hx0 τ i.succ
    have hne2 := FlowCoefficientBounds.dmin_ne X hx0 τ i.castSucc
    exact (hd1.div hd2 hne2).norm.rpow_const (Or.inl (norm_ne_zero_iff.mpr (div_ne_zero hne1 hne2)))
  unfold Data.nfac
  exact tendsto_finset_prod _ fun τ _ => tendsto_finset_prod _ fun i _ => h τ i

/- English proof (translation)
Establish `hset : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩ ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re})`. Use extensionality with `x`. Simplify using `[Data.dom, GG]`. Rewrite using `[hset]`. Use `isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)` and prove the remaining obligations.

Conclude with `isOpen_ne_fun ((show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det) continuous_const`. Conclude with `isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (cont_dmin X τ i)))`.
-/
private theorem isOpen_dom_upper_bounds : IsOpen X.dom := by
  have hset : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [Data.dom, GG]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun
      ((show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det)
      continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp (cont_dmin X τ i)))

/- English proof (translation)
Introduce `x0 hx0`. Take `⟨-, C, hC⟩` from `hP`. Establish `hpos` using `FlowCoefficientBounds.nfac_pos X hx0 la`. Establish `hcont` using `continuousAt_nfac X la hx0`. Establish `hev : ∀ᶠ z in 𝓝 x0, X.nfac la x0 / 2 < X.nfac la z ∧ z ∈ X.dom` using `(hcont.eventually (lt_mem_nhds (by linarith : X.nfac la x0 / 2 < X.nfac la x0))).and ((isOpen_dom_upper_bounds X).mem_nhds hx0)`.

Take `⟨ρ, hρ, hball⟩` from `Metric.mem_nhds_iff.mp hev`. Use `⟨ρ / 2, by positivity, 2 * C / X.nfac la x0, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Conclude with `(hball (Metric.closedBall_subset_ball (by linarith) hz)).2`. Introduce `t z hz`.

Establish `hz'` using `hball (Metric.closedBall_subset_ball (by linarith) hz)`. Take `⟨hfd, hfn⟩` from `FlowCoefficientBounds.flow_real X hξ hz'.2 t la`. Establish `h1` using `hC _ hfd`. Rewrite using `[flowL_apply]`. Establish `h2 : X.pnorm la P (X.flow ξ (fun τ => (t τ : ℂ)) z) = ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * X.nfac la z`.

Rewrite using `[← hfn]`. Both sides reduce to the same expression. Rewrite `h1` using `[h2]`. Establish `h3 : ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * (X.nfac la x0 / 2) ≤ ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * X.nfac la z` using `mul_le_mul_of_nonneg_left hz'.1.le (norm_nonneg _)`. Rewrite using `[le_div_iff₀ hpos]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma fj_hbd (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) : ∀ x0 ∈ X.dom, ∃ ρ > 0, ∃ C, closedBall x0 ρ ⊆ X.dom ∧
      ∀ t : X.Ψ → ℝ, ∀ z ∈ closedBall x0 ρ, ‖P (flowL X ξ t z)‖ ≤ C := by
  intro x0 hx0
  obtain ⟨-, C, hC⟩ := hP
  have hpos := FlowCoefficientBounds.nfac_pos X hx0 la
  have hcont := continuousAt_nfac X la hx0
  have hev : ∀ᶠ z in 𝓝 x0, X.nfac la x0 / 2 < X.nfac la z ∧ z ∈ X.dom :=
    (hcont.eventually (lt_mem_nhds (by linarith : X.nfac la x0 / 2 < X.nfac la x0))).and
      ((isOpen_dom_upper_bounds X).mem_nhds hx0)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ρ / 2, by positivity, 2 * C / X.nfac la x0, ?_, ?_⟩
  · intro z hz
    exact (hball (Metric.closedBall_subset_ball (by linarith) hz)).2
  · intro t z hz
    have hz' := hball (Metric.closedBall_subset_ball (by linarith) hz)
    obtain ⟨hfd, hfn⟩ := FlowCoefficientBounds.flow_real X hξ hz'.2 t la
    have h1 := hC _ hfd
    rw [flowL_apply]
    have h2 : X.pnorm la P (X.flow ξ (fun τ => (t τ : ℂ)) z) =
        ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * X.nfac la z := by
      rw [← hfn]
      rfl
    rw [h2] at h1
    have h3 : ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * (X.nfac la x0 / 2) ≤
        ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * X.nfac la z :=
      mul_le_mul_of_nonneg_left hz'.1.le (norm_nonneg _)
    rw [le_div_iff₀ hpos]
    linarith

/- English proof (translation)
Unfold `Data.fj`. Use `split_ifs with h1 h2`. Apply `DifferentiableOn.const_mul` to reduce the goal to its premises. Establish `he1 : ∀ s : X.Ψ → ℝ, ‖cexp (-(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))‖ ≤ 1`. Introduce `s`.

Establish `hre : -(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ) = ((-(4 * Real.pi * ∑ τ, ν τ * s τ) : ℝ) : ℂ) * I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hre, Complex.norm_exp_ofReal_mul_I]`. Establish `hec : Continuous fun s : X.Ψ → ℝ => cexp (-(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))` using `by first`.

Consider the case `fun_prop`. Consider the case `continuity`. Conclude with `diffOn_param_bdd h2.choose_spec.2.2.2 (flowL X ξ) (cont_flowL X ξ) (isOpen_dom_upper_bounds X) (fun t x hx => (FlowCoefficientBounds.flow_real X hξ hx t la).1) P hP.1.1 _ hec he1 (fj_hbd X la P hP hξ)`. Conclude with `differentiableOn_const 0`. Conclude with `differentiableOn_const 0`.
-/
theorem fj_diffOn (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) : DifferentiableOn ℂ (X.fj la ξ ν P) X.dom := by
  unfold Data.fj
  split_ifs with h1 h2
  · apply DifferentiableOn.const_mul
    have he1 : ∀ s : X.Ψ → ℝ, ‖cexp (-(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))‖ ≤ 1 := by
      intro s
      have hre : -(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ) =
          ((-(4 * Real.pi * ∑ τ, ν τ * s τ) : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [hre, Complex.norm_exp_ofReal_mul_I]
    have hec : Continuous fun s : X.Ψ → ℝ => cexp (-(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ)) := by
      first
      | fun_prop
      | continuity
    exact diffOn_param_bdd h2.choose_spec.2.2.2 (flowL X ξ) (cont_flowL X ξ) (isOpen_dom_upper_bounds X)
      (fun t x hx => (FlowCoefficientBounds.flow_real X hξ hx t la).1) P hP.1.1 _ hec he1 (fj_hbd X la P hP hξ)
  · exact differentiableOn_const 0
  · exact differentiableOn_const 0

end Frame

end

end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
