import Mathlib

open MeasureTheory Topology

universe u

namespace GlobalTheory.CompanionTheory.EisTube

noncomputable def ker {ι : Type} [Fintype ι] (z : ι → ℂ) (t : ι → ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)

/- English proof (translation)
Establish `h1 : Integrable (fun x : ℝ => Real.exp (-c * |x|))`. Establish `h1 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Ioi 0)` using `(exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi`. Establish `h2 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Iic 0)` using `(integrableOn_exp_mul_Iic hc 0).congr_fun (fun x hx => by rw [abs_of_nonpos hx, neg_mul_neg]) measurableSet_Iic`. Establish `h3` using `h2.union h1`. Rewrite `h3` using `[Set.Iic_union_Ioi, integrableOn_univ]`.

Conclude with `h3`. Establish `hI : Integrable (fun t : ι → ℝ => ∏ i, Real.exp (-c * |t i|)) (Measure.pi fun _ => volume)` using `Integrable.fintype_prod (f := fun _ x => Real.exp (-c * |x|)) fun _ => h1`. Rewrite using `[volume_pi]`. Use `hI.congr (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [← Real.exp_sum, neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]`.
-/
theorem integrable_exp_neg_sum_abs {ι : Type} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ι → ℝ => Real.exp (-(c * ∑ i, |t i|))) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
    have h2 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Iic 0) :=
      (integrableOn_exp_mul_Iic hc 0).congr_fun (fun x hx => by rw [abs_of_nonpos hx, neg_mul_neg])
        measurableSet_Iic
    have h3 := h2.union h1
    rw [Set.Iic_union_Ioi, integrableOn_univ] at h3
    exact h3
  have hI : Integrable (fun t : ι → ℝ => ∏ i, Real.exp (-c * |t i|)) (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (f := fun _ x => Real.exp (-c * |x|)) fun _ => h1
  rw [volume_pi]
  refine hI.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [← Real.exp_sum, neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]

/- English proof (translation)
Use `choose Cf hCf using hψ`. Set `vec : (ι → Bool) → ι → ℝ` to `fun σ i => R * (if σ i then 1 else -1)`. Use `⟨∑ σ : ι → Bool, |Cf (vec σ)|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun p t => ?_⟩` and prove the remaining obligations. Set `σ : ι → Bool` to `fun i => decide (0 ≤ t i)`. Establish `hs : ∑ i, vec σ i * t i = R * ∑ i, |t i|`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : 0 ≤ t i`. Simplify using `[vec, σ, hi, abs_of_nonneg hi]`. Establish `hi' : t i < 0` using `not_le.mp hi`.

Simplify using `[vec, σ, hi, abs_of_neg hi']`. Establish `h1` using `hCf (vec σ) p t`. Rewrite `h1` using `[hs]`. Use `h1.trans ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le` and prove the remaining obligations.

Use `mul_le_mul_of_nonneg_right ?_ (hh p)` and prove the remaining obligations. Conclude with `(le_abs_self _).trans (Finset.single_le_sum (f := fun σ : ι → Bool => |Cf (vec σ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ))`.
-/
theorem uniform_bound {ι : Type} [Fintype ι] {P : Type u} {h : P → ℝ} (hh : ∀ p, 0 ≤ h p)
    {ψ : P → (ι → ℝ) → ℂ}
    (hψ : ∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i)))
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * (R * ∑ i, |t i|))) := by
  classical
  choose Cf hCf using hψ
  let vec : (ι → Bool) → ι → ℝ := fun σ i => R * (if σ i then 1 else -1)
  refine ⟨∑ σ : ι → Bool, |Cf (vec σ)|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun p t => ?_⟩
  let σ : ι → Bool := fun i => decide (0 ≤ t i)
  have hs : ∑ i, vec σ i * t i = R * ∑ i, |t i| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 0 ≤ t i
    · simp [vec, σ, hi, abs_of_nonneg hi]
    · have hi' : t i < 0 := not_le.mp hi
      simp [vec, σ, hi, abs_of_neg hi']
  have h1 := hCf (vec σ) p t
  rw [hs] at h1
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_right ?_ (hh p)
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ : ι → Bool => |Cf (vec σ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ))

/- English proof (translation)
Rewrite using `[ker, Complex.norm_exp]`. Use `Real.exp_le_exp.mpr ?_` and prove the remaining obligations. Establish `h1 : (2 * (Real.pi : ℂ) * ∑ i, z i * t i).re = 2 * Real.pi * ∑ i, (z i).re * t i`. Establish `: (2 * (Real.pi : ℂ) * ∑ i, z i * t i) = ((2 * Real.pi : ℝ) : ℂ) * ∑ i, z i * t i` using `by push_cast; ring`. Rewrite using `[this, Complex.re_ofReal_mul, Complex.re_sum]`.

Simplify using the standard rewrite rules. Rewrite using `[h1]`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_ker_le {ι : Type} [Fintype ι] {z : ι → ℂ} {B : ℝ} (hz : ∀ i, |(z i).re| ≤ B)
    (t : ι → ℝ) : ‖ker z t‖ ≤ Real.exp (2 * Real.pi * (B * ∑ i, |t i|)) := by
  rw [ker, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have h1 : (2 * (Real.pi : ℂ) * ∑ i, z i * t i).re = 2 * Real.pi * ∑ i, (z i).re * t i := by
    have : (2 * (Real.pi : ℂ) * ∑ i, z i * t i) = ((2 * Real.pi : ℝ) : ℂ) * ∑ i, z i * t i := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul, Complex.re_sum]
    simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (z i).re * t i ≤ |(z i).re * t i| := le_abs_self _
    _ = |(z i).re| * |t i| := abs_mul _ _
    _ ≤ B * |t i| := mul_le_mul_of_nonneg_right (hz i) (abs_nonneg _)

/- English proof (translation)
Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dom_bound {ι : Type} [Fintype ι] {P : Type u} {h : P → ℝ} (hh : ∀ p, 0 ≤ h p)
    {ψ : P → (ι → ℝ) → ℂ} {C B : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ((B + 1) * ∑ i, |t i|))))
    {z : ι → ℂ} (hz : ∀ i, |(z i).re| ≤ B) (p : P) (t : ι → ℝ) :
    ‖ψ p t * ker z t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := by
  rw [norm_mul]
  calc ‖ψ p t‖ * ‖ker z t‖
      ≤ (C * h p * Real.exp (-(2 * Real.pi * ((B + 1) * ∑ i, |t i|)))) *
          Real.exp (2 * Real.pi * (B * ∑ i, |t i|)) :=
        mul_le_mul (hC p t) (norm_ker_le hz t) (norm_nonneg _)
          (mul_nonneg (mul_nonneg hC0 (hh p)) (Real.exp_pos _).le)
    _ = C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/- English proof (translation)
Unfold `ker`. Use `fun_prop`.
-/
theorem continuous_ker_right {ι : Type} [Fintype ι] (z : ι → ℂ) : Continuous (ker z) := by
  unfold ker
  fun_prop

/- English proof (translation)
Unfold `ker`. Use `fun_prop`.
-/
theorem continuous_ker_left {ι : Type} [Fintype ι] (t : ι → ℝ) :
    Continuous (fun z : ι → ℂ => ker z t) := by
  unfold ker
  fun_prop

/- English proof (translation)
The claim follows from `|(z i).re| ≤ (∑ j, |(z₀ j).re|) + 1 := by have h1 : ‖z i - z₀ i‖ ≤ ‖z - z₀‖ := norm_le_pi_norm (z - z₀) i have h2 : ‖z - z₀‖ < 1 := by rwa [← dist_eq_norm] have h3 : |(z i - z₀ i).re| ≤ ‖z i - z₀ i‖ := Complex.abs_re_le_norm _ have h4 : |(z₀ i).re| ≤ ∑ j, |(z₀ j).re| := Finset.si …`.
-/
theorem re_le_of_dist {ι : Type} [Fintype ι] {z z₀ : ι → ℂ} (hz : dist z z₀ < 1) (i : ι) :
    |(z i).re| ≤ (∑ j, |(z₀ j).re|) + 1 := by
  have h1 : ‖z i - z₀ i‖ ≤ ‖z - z₀‖ := norm_le_pi_norm (z - z₀) i
  have h2 : ‖z - z₀‖ < 1 := by rwa [← dist_eq_norm]
  have h3 : |(z i - z₀ i).re| ≤ ‖z i - z₀ i‖ := Complex.abs_re_le_norm _
  have h4 : |(z₀ i).re| ≤ ∑ j, |(z₀ j).re| :=
    Finset.single_le_sum (f := fun j => |(z₀ j).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h5 : |(z i).re| ≤ |(z i - z₀ i).re| + |(z₀ i).re| := by
    have : (z i).re = (z i - z₀ i).re + (z₀ i).re := by simp
    rw [this]
    simpa using abs_add_le (z i - z₀ i).re (z₀ i).re
  linarith

noncomputable def lin {ι : Type} [Fintype ι] (t : ι → ℝ) : (ι → ℂ) →L[ℂ] ℂ :=
  (2 * (Real.pi : ℂ)) • ∑ i, (t i : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i

/- English proof (translation)
Simplify using `[lin, mul_comm]`.
-/
theorem lin_apply {ι : Type} [Fintype ι] (t : ι → ℝ) (z : ι → ℂ) :
    lin t z = 2 * (Real.pi : ℂ) * ∑ i, z i * t i := by
  simp [lin, mul_comm]

/- English proof (translation)
Unfold `lin`. Use `fun_prop`.
-/
theorem continuous_lin {ι : Type} [Fintype ι] : Continuous (lin (ι := ι)) := by
  unfold lin
  fun_prop

/- English proof (translation)
Establish `h00 : 0 ≤ 2 * Real.pi * ∑ i, |t i|` using `by positivity`. Use `ContinuousLinearMap.opNorm_le_bound _ h00 fun z => ?_` and prove the remaining obligations. Rewrite using `[lin_apply, norm_mul]`. Establish `h0 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi`. Simplify using `[abs_of_pos Real.pi_pos]`.

Establish `h2pi : (0 : ℝ) ≤ 2 * Real.pi` using `by positivity`. Rewrite using `[h0, mul_assoc (2 * Real.pi)]`. Use `mul_le_mul_of_nonneg_left ?_ h2pi` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, mul_comm, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)`.
-/
theorem norm_lin_le {ι : Type} [Fintype ι] (t : ι → ℝ) :
    ‖lin t‖ ≤ 2 * Real.pi * ∑ i, |t i| := by
  have h00 : 0 ≤ 2 * Real.pi * ∑ i, |t i| := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h00 fun z => ?_
  rw [lin_apply, norm_mul]
  have h0 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [h0, mul_assoc (2 * Real.pi)]
  refine mul_le_mul_of_nonneg_left ?_ h2pi
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_comm, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun z : ι → ℂ => lin t z) (lin t) z` using `(lin t).hasFDerivAt`. Establish `h2` using `(h1.cexp).const_mul w`. Establish `e : (fun z : ι → ℂ => w * ker z t) = fun z => w * Complex.exp (lin t z)`. Use function extensionality and compare the values at `z`. Simplify using `only [ker, lin_apply]`.

Establish `e2 : (w * ker z t) • lin t = w • Complex.exp (lin t z) • lin t`. Rewrite using `[smul_smul, ker, lin_apply]`. Rewrite using `[e, e2]`. Conclude with `h2`.
-/
theorem hasFDerivAt_ker {ι : Type} [Fintype ι] (w : ℂ) (t : ι → ℝ) (z : ι → ℂ) :
    HasFDerivAt (fun z : ι → ℂ => w * ker z t) ((w * ker z t) • lin t) z := by
  have h1 : HasFDerivAt (fun z : ι → ℂ => lin t z) (lin t) z := (lin t).hasFDerivAt
  have h2 := (h1.cexp).const_mul w
  have e : (fun z : ι → ℂ => w * ker z t) = fun z => w * Complex.exp (lin t z) := by
    funext z; simp only [ker, lin_apply]
  have e2 : (w * ker z t) • lin t = w • Complex.exp (lin t z) • lin t := by
    rw [smul_smul, ker, lin_apply]
  rw [e, e2]
  exact h2

/- English proof (translation)
Establish `h1 : S ≤ Real.exp S` using `by linarith [Real.add_one_le_exp S]`. Combine the equalities or inequalities in the displayed calculation. Use `Real.exp_le_exp.mpr ?_` and prove the remaining obligations. Use polynomial arithmetic with `[Real.pi_gt_three]`.
-/
theorem mul_exp_le {S : ℝ} (hS : 0 ≤ S) :
    S * Real.exp (-(2 * Real.pi * S)) ≤ Real.exp (-S) := by
  have h1 : S ≤ Real.exp S := by linarith [Real.add_one_le_exp S]
  calc S * Real.exp (-(2 * Real.pi * S))
      ≤ Real.exp S * Real.exp (-(2 * Real.pi * S)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (S + -(2 * Real.pi * S)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-S) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [Real.pi_gt_three]

/- English proof (translation)
Establish `h2pi : (0 : ℝ) < 2 * Real.pi` using `by positivity`. Establish `hG : Integrable (fun t : ι → ℝ => Real.exp (-(2 * Real.pi * ∑ i, |t i|)))` using `integrable_exp_neg_sum_abs h2pi`. Establish `hmeas : ∀ p (z : ι → ℂ), AEStronglyMeasurable (fun t => ψ p t * ker z t)` using `fun p z => (hm p).mul (continuous_ker_right z).aestronglyMeasurable`. Establish `hI : ∀ p (z : ι → ℂ), Integrable (fun t => ψ p t * ker z t)`. Introduce `p z`.

Take `⟨C, hC0, hC⟩` from `uniform_bound hh hv ((∑ j, |(z j).re|) + 1 + 1)`. Establish `hz : ∀ i, |(z i).re| ≤ (∑ j, |(z j).re|) + 1` using `fun i => re_le_of_dist (by simp) i`. Conclude with `Integrable.mono' (hG.const_mul (C * h p)) (hmeas p z) (Filter.Eventually.of_forall fun t => dom_bound hh hC0 hC hz p t)`. Use `⟨hI, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p z₀`.

Express the relevant statement in the definitionally equal form `DifferentiableAt ℂ (fun z : ι → ℂ => ∫ t : ι → ℝ, ψ p t * ker z t) z₀`. Take `⟨C, hC0, hC⟩` from `uniform_bound hh hv ((∑ j, |(z₀ j).re|) + 1 + 1)`. Establish `hb : ∀ t : ι → ℝ, ∀ z ∈ Metric.ball z₀ 1, ‖(ψ p t * ker z t) • lin t‖ ≤ C * h p * (2 * Real.pi) * Real.exp (-(1 * ∑ i, |t i|))`. Introduce `t z hz`. Establish `hS : 0 ≤ ∑ i, |t i|` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`.

Establish `hCh : 0 ≤ C * h p` using `mul_nonneg hC0 (hh p)`. Rewrite using `[norm_smul, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `key` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := volume) (F := fun (z : ι → ℂ) (t : ι → ℝ) => ψ p t * ker z t) (F' := fun (z : ι → ℂ) (t : ι → ℝ) => (ψ p t * ker z t) • lin t) (x₀ := z₀) (s := Metric.ball z₀ 1) (bound := fun t => C * h p * (2 * Real.pi) * Real.exp (- …`. Conclude with `key.differentiableAt`.

Express the relevant statement in the definitionally equal form `Continuous (fun q : (ι → ℂ) × P => ∫ t : ι → ℝ, ψ q.2 t * ker q.1 t)`. Rewrite using `[continuous_iff_continuousAt]`. Introduce and unpack `⟨z₀, p₀⟩`. Take `⟨U, hU, M, hM⟩` from `hloc p₀`. Take `⟨C, hC0, hC⟩` from `uniform_bound hh hv ((∑ j, |(z₀ j).re|) + 1 + 1)`.

Establish `hev : ∀ᶠ q : (ι → ℂ) × P in 𝓝 (z₀, p₀), dist q.1 z₀ < 1 ∧ q.2 ∈ U` using `((continuous_fst.tendsto (z₀, p₀)).eventually (Metric.ball_mem_nhds z₀ one_pos)).and ((continuous_snd.tendsto (z₀, p₀)).eventually hU)`. Use `continuousAt_of_dominated (bound := fun t => C * M * Real.exp (-(2 * Real.pi * ∑ i, |t i|))) (Filter.Eventually.of_forall fun q => hmeas q.2 q.1) (hev.mono fun q hq => Filter.Eventually.of_forall fun t => ?_) (hG.const_mul (C * M)) (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Conclude with `(dom_bound hh hC0 hC (re_le_of_dist hq.1) q.2 t).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM ⟨_, hq.2, rfl⟩) hC0) (Real.exp_pos _).le)`. Conclude with `(((hc t).comp continuous_snd).mul ((continuous_ker_left t).comp continuous_fst)).continuousAt`. Introduce `K hK`.

Take `⟨R, hR⟩` from `hK.isBounded.exists_norm_le`. Establish `hz : ∀ z ∈ K, ∀ i, |(z i).re| ≤ R` using `fun z hzK i => (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm z i).trans (hR z hzK))`. Take `⟨C, hC0, hC⟩` from `uniform_bound hh hv (R + 1)`. Use `⟨C * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|)), fun z hzK p => ?_⟩` and prove the remaining obligations. Establish `key` using `norm_integral_le_of_norm_le (hG.const_mul (C * h p)) (Filter.Eventually.of_forall fun t => dom_bound hh hC0 hC (hz z hzK) p t)`.

Rewrite `key` using `[integral_const_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem laplaceEntire (ι : Type) [Fintype ι] (P : Type u) [TopologicalSpace P]
    [FirstCountableTopology P] (h : P → ℝ) (hh : ∀ p, 0 ≤ h p)
    (hloc : ∀ p, ∃ U ∈ nhds p, BddAbove (h '' U))
    (ψ : P → (ι → ℝ) → ℂ) (hm : ∀ p, MeasureTheory.AEStronglyMeasurable (ψ p))
    (hc : ∀ t, Continuous (fun p => ψ p t))
    (hv : ∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t,
      ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i))) :
    (∀ p (z : ι → ℂ), MeasureTheory.Integrable
        (fun t : ι → ℝ => ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    (∀ p, Differentiable ℂ (fun z : ι → ℂ =>
        ∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    Continuous (fun q : (ι → ℂ) × P =>
        ∫ t : ι → ℝ, ψ q.2 t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, q.1 i * t i)) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p,
        ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖ ≤ C * h p) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hG : Integrable (fun t : ι → ℝ => Real.exp (-(2 * Real.pi * ∑ i, |t i|))) :=
    integrable_exp_neg_sum_abs h2pi
  have hmeas : ∀ p (z : ι → ℂ), AEStronglyMeasurable (fun t => ψ p t * ker z t) := fun p z =>
    (hm p).mul (continuous_ker_right z).aestronglyMeasurable
  have hI : ∀ p (z : ι → ℂ), Integrable (fun t => ψ p t * ker z t) := by
    intro p z
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv ((∑ j, |(z j).re|) + 1 + 1)
    have hz : ∀ i, |(z i).re| ≤ (∑ j, |(z j).re|) + 1 := fun i =>
      re_le_of_dist (by simp) i
    exact Integrable.mono' (hG.const_mul (C * h p)) (hmeas p z)
      (Filter.Eventually.of_forall fun t => dom_bound hh hC0 hC hz p t)
  refine ⟨hI, ?_, ?_, ?_⟩
  · intro p z₀
    change DifferentiableAt ℂ (fun z : ι → ℂ => ∫ t : ι → ℝ, ψ p t * ker z t) z₀
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv ((∑ j, |(z₀ j).re|) + 1 + 1)
    have hb : ∀ t : ι → ℝ, ∀ z ∈ Metric.ball z₀ 1,
        ‖(ψ p t * ker z t) • lin t‖ ≤ C * h p * (2 * Real.pi) * Real.exp (-(1 * ∑ i, |t i|)) := by
      intro t z hz
      have hS : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hCh : 0 ≤ C * h p := mul_nonneg hC0 (hh p)
      rw [norm_smul, one_mul]
      calc ‖ψ p t * ker z t‖ * ‖lin t‖
          ≤ (C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|))) * (2 * Real.pi * ∑ i, |t i|) :=
            mul_le_mul (dom_bound hh hC0 hC (re_le_of_dist hz) p t) (norm_lin_le t) (norm_nonneg _)
              (mul_nonneg hCh (Real.exp_pos _).le)
        _ = C * h p * (2 * Real.pi) *
              ((∑ i, |t i|) * Real.exp (-(2 * Real.pi * ∑ i, |t i|))) := by ring
        _ ≤ C * h p * (2 * Real.pi) * Real.exp (-∑ i, |t i|) :=
            mul_le_mul_of_nonneg_left (mul_exp_le hS) (mul_nonneg hCh h2pi.le)
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := volume)
      (F := fun (z : ι → ℂ) (t : ι → ℝ) => ψ p t * ker z t)
      (F' := fun (z : ι → ℂ) (t : ι → ℝ) => (ψ p t * ker z t) • lin t) (x₀ := z₀)
      (s := Metric.ball z₀ 1)
      (bound := fun t => C * h p * (2 * Real.pi) * Real.exp (-(1 * ∑ i, |t i|)))
      (Metric.ball_mem_nhds _ one_pos) (Filter.Eventually.of_forall fun z => hmeas p z) (hI p z₀)
      ((hmeas p z₀).smul continuous_lin.aestronglyMeasurable)
      (Filter.Eventually.of_forall hb)
      ((integrable_exp_neg_sum_abs one_pos).const_mul _)
      (Filter.Eventually.of_forall fun t z _ => hasFDerivAt_ker (ψ p t) t z)
    exact key.differentiableAt
  · change Continuous (fun q : (ι → ℂ) × P => ∫ t : ι → ℝ, ψ q.2 t * ker q.1 t)
    rw [continuous_iff_continuousAt]
    rintro ⟨z₀, p₀⟩
    obtain ⟨U, hU, M, hM⟩ := hloc p₀
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv ((∑ j, |(z₀ j).re|) + 1 + 1)
    have hev : ∀ᶠ q : (ι → ℂ) × P in 𝓝 (z₀, p₀), dist q.1 z₀ < 1 ∧ q.2 ∈ U :=
      ((continuous_fst.tendsto (z₀, p₀)).eventually (Metric.ball_mem_nhds z₀ one_pos)).and
        ((continuous_snd.tendsto (z₀, p₀)).eventually hU)
    refine continuousAt_of_dominated
      (bound := fun t => C * M * Real.exp (-(2 * Real.pi * ∑ i, |t i|)))
      (Filter.Eventually.of_forall fun q => hmeas q.2 q.1)
      (hev.mono fun q hq => Filter.Eventually.of_forall fun t => ?_)
      (hG.const_mul (C * M)) (Filter.Eventually.of_forall fun t => ?_)
    · exact (dom_bound hh hC0 hC (re_le_of_dist hq.1) q.2 t).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM ⟨_, hq.2, rfl⟩) hC0) (Real.exp_pos _).le)
    · exact (((hc t).comp continuous_snd).mul
        ((continuous_ker_left t).comp continuous_fst)).continuousAt
  · intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have hz : ∀ z ∈ K, ∀ i, |(z i).re| ≤ R := fun z hzK i =>
      (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm z i).trans (hR z hzK))
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv (R + 1)
    refine ⟨C * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|)), fun z hzK p => ?_⟩
    have key := norm_integral_le_of_norm_le (hG.const_mul (C * h p))
      (Filter.Eventually.of_forall fun t => dom_bound hh hC0 hC (hz z hzK) p t)
    rw [integral_const_mul] at key
    calc ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖
        ≤ C * h p * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := key
      _ = (C * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|))) * h p := by ring

end GlobalTheory.CompanionTheory.EisTube
