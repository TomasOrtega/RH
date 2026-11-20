import Mathlib

open scoped ContDiff
open MeasureTheory Set Filter Topology Metric

noncomputable section

namespace GlobalTheory.SchwartzDiv

section Param

variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}

/- English proof (translation)
Establish `hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1` using `ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst) (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl`. Establish `hΘ'` using `hΘs.continuous`. Establish `hK : IsCompact (closedBall t₀ 1 ×ˢ S)` using `(isCompact_closedBall t₀ 1).prod hS`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hΘ'.continuousOn`. Take `⟨C₀, hC₀⟩` from `hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn`.

Establish `hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν` using `fun t => hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)`. Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C) (ball_mem_nhds t₀ one_pos) (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_` and prove the remaining obligations. Use `Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_ filter_upwards [hcS] with y hy` and prove the remaining obligations. Rewrite using `[norm_smul]`. Conclude with `mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)`.

Conclude with `hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)`. Use `filter_upwards [hcS] with y hy t ht`. Rewrite using `[norm_smul]`. Conclude with `mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)`. Use `.of_forall fun y t _ => ?_` and prove the remaining obligations.

Establish `hd : ContDiff ℝ ∞ fun s => Θ (s, c y)` using `hΘ.comp (contDiff_id.prodMk contDiff_const)`. Conclude with `((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)`.
-/
theorem hasFDerivAt_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) (t₀ : P) :
    HasFDerivAt (fun t => ∫ y, φ y • Θ (t, c y) ∂ν) (∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t₀ ∂ν) t₀ := by
  have hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
    ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
      (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
  have hΘ' := hΘs.continuous
  have hK : IsCompact (closedBall t₀ 1 ×ˢ S) := (isCompact_closedBall t₀ 1).prod hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ'.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn
  have hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν := fun t =>
    hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C)
    (ball_mem_nhds t₀ one_pos) (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_
  · refine Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_
    filter_upwards [hcS] with y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)
  · exact hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  · filter_upwards [hcS] with y hy t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)
  · refine .of_forall fun y t _ => ?_
    have hd : ContDiff ℝ ∞ fun s => Θ (s, c y) := hΘ.comp (contDiff_id.prodMk contDiff_const)
    exact ((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)

/- English proof (translation)
Rewrite using `[contDiff_infty]`. Introduce `n`. Proceed by induction on `n generalizing W with`. Consider the case `zero`. Conclude with `contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)`.

Consider the case `succ n ih`. Establish `hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1` using `ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst) (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl`. Conclude with `contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν, ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩`.
-/
theorem contDiff_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by
  rw [contDiff_infty]
  intro n
  induction n generalizing W with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)
  | succ n ih =>
    have hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
      ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
        (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν,
      ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩

end Param

def invCut (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1) * t⁻¹

/- English proof (translation)
Rewrite using `[invCut, Real.smoothTransition.one_of_one_le (by linarith), one_mul]`.
-/
theorem invCut_of_one_le {t : ℝ} (ht : 1 ≤ t) : invCut t = t⁻¹ := by
  rw [invCut, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

/- English proof (translation)
Rewrite using `[invCut, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]`.
-/
theorem invCut_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : invCut t = 0 := by
  rw [invCut, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

/- English proof (translation)
Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `t`. Break down `lt_or_ge 0 t with h | h` into its components or cases. Conclude with `((Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt).mul (contDiffAt_inv ℝ h.ne')`. Establish `: invCut =ᶠ[𝓝 t] fun _ => 0` using `by filter_upwards [Iio_mem_nhds (show t < 1 / 2 by linarith)] with s hs`.

Conclude with `invCut_of_le_half hs.le`. Conclude with `contDiffAt_const.congr_of_eventuallyEq this`.
-/
theorem contDiff_invCut : ContDiff ℝ ∞ invCut := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge 0 t with h | h
  · exact ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt).mul (contDiffAt_inv ℝ h.ne')
  · have : invCut =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show t < 1 / 2 by linarith)] with s hs
      exact invCut_of_le_half hs.le
    exact contDiffAt_const.congr_of_eventuallyEq this

/- English proof (translation)
Use `⟨contDiff_invCut, fun n => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `(isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).exists_bound_of_continuousOn (contDiff_invCut.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn`. Use `⟨0, max C (Nat.factorial n : ℝ), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, mul_one]`. Break down `lt_or_ge x (1 / 2) with h1 | h1` into its components or cases.

Establish `: invCut =ᶠ[𝓝 x] fun _ => (0 : ℝ)` using `by filter_upwards [Iio_mem_nhds h1] with s hs`. Conclude with `invCut_of_le_half hs.le`. Rewrite using `[(this.iteratedFDeriv ℝ n).eq_of_nhds]`. Simplify using `only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]`. Conclude with `le_max_of_le_right (Nat.cast_nonneg _)`.

Break down `le_or_gt x 2 with h2 | h2` into its components or cases. Conclude with `(hC x ⟨h1, h2⟩).trans (le_max_left _ _)`. Establish `: invCut =ᶠ[𝓝 x] Inv.inv` using `by filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < x by linarith)] with s hs`. Conclude with `invCut_of_one_le hs.le`. Rewrite using `[(this.iteratedFDeriv ℝ n).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]`.

Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Establish `hx : ‖x ^ (-1 - n : ℤ)‖ ≤ 1`. Rewrite using `[Real.norm_eq_abs, abs_of_pos (zpow_pos (by linarith) _)]`. Conclude with `zpow_le_one_of_nonpos₀ (by linarith) (by omega)`. Rewrite using `[norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem hasTemperateGrowth_invCut : invCut.HasTemperateGrowth := by
  refine ⟨contDiff_invCut, fun n => ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (contDiff_invCut.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn
  refine ⟨0, max C (Nat.factorial n : ℝ), fun x => ?_⟩
  rw [pow_zero, mul_one]
  rcases lt_or_ge x (1 / 2) with h1 | h1
  · have : invCut =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      exact invCut_of_le_half hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds]
    simp only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact le_max_of_le_right (Nat.cast_nonneg _)
  rcases le_or_gt x 2 with h2 | h2
  · exact (hC x ⟨h1, h2⟩).trans (le_max_left _ _)
  · have : invCut =ᶠ[𝓝 x] Inv.inv := by
      filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < x by linarith)] with s hs
      exact invCut_of_one_le hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, iter_deriv_inv]
    refine le_trans ?_ (le_max_right _ _)
    have hx : ‖x ^ (-1 - n : ℤ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (zpow_pos (by linarith) _)]
      exact zpow_le_one_of_nonpos₀ (by linarith) (by omega)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
    calc (Nat.factorial n : ℝ) * ‖x ^ (-1 - n : ℤ)‖ ≤ Nat.factorial n * 1 := by gcongr
      _ = Nat.factorial n := mul_one _

end GlobalTheory.SchwartzDiv

namespace GlobalTheory.SchwartzDiv

/- English proof (translation)
Set `b` to `Module.finBasis ℝ V`. Set `L : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ` to `fun i => LinearMap.toContinuousLinearMap (b.coord i)`. Establish `hL : ∀ i x, L i x = b.repr x i` using `fun i x => by simp [L, Module.Basis.coord_apply]`. Set `q : V → ℝ` to `fun x => ∑ i, L i x ^ 2`. Establish `hq : q.HasTemperateGrowth`.

Simplify using `only [q]`. Conclude with `Function.HasTemperateGrowth.sum fun i _ => ((L i).hasTemperateGrowth).pow 2`. Establish `hqs : ContDiff ℝ ∞ q` using `hq.1`. Establish `hfs : ContDiff ℝ ∞ f` using `f.smooth ⊤`. Establish `hfd : ContDiff ℝ ∞ (fderiv ℝ f)` using `hfs.fderiv_right (by simp)`.

Set `k : Fin (Module.finrank ℝ V) → V → ℂ` to `fun i x => ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) (b i)`. Establish `hk : ∀ i, ContDiff ℝ ∞ (k i)`. Introduce `i`. Establish `hΘ : ContDiff ℝ ∞ fun p : V × ℝ => fderiv ℝ f (p.2 • p.1) (b i)` using `(hfd.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_const`. Establish `key` using `contDiff_integral_smul_param (ν := volume.restrict (Ioc (0 : ℝ) 1)) (c := id) (S := Icc (0 : ℝ) 1) (φ := fun _ => (1 : ℂ)) aestronglyMeasurable_id isCompact_Icc ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => Ioc_subset_Icc_self ht) (integrableOn_const (by simp)) hΘ`.

Use `key using 2 with x` and compare the differences between its conclusion and the goal. Simplify using `[k, intervalIntegral.integral_of_le zero_le_one]`. Establish `key : ∀ x, f x = ∑ i, (L i x : ℂ) * k i x`. Introduce `x`. Establish `hc : ∀ v : V, Continuous fun t : ℝ => fderiv ℝ f (t • x) v` using `fun v => (hfd.continuous.comp (continuous_id.smul continuous_const)).clm_apply continuous_const`.

Establish `h1 : ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) x = f ((1 : ℝ) • x) - f ((0 : ℝ) • x)`. Use `intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => f (t • x)) (fun t _ => ?_) ((hc x).intervalIntegrable _ _)` and prove the remaining obligations. Use `(f.differentiableAt (x := t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)` as an intermediate fact. Simplify using `only [one_smul] at this`. Conclude with `this`.

Rewrite `h1` using `[one_smul, zero_smul, hf0, sub_zero]`. Rewrite using `[← h1]`. Establish `h2 : ∀ t : ℝ, fderiv ℝ f (t • x) x = ∑ i, (L i x : ℂ) * fderiv ℝ f (t • x) (b i)`. Introduce `t`. Rewrite using `[show fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ i, b.repr x i • b i) by rw [b.sum_repr], map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Complex.real_smul, hL]`. Repeatedly rewrite using `[h2]`. Rewrite using `[intervalIntegral.integral_finset_sum (f := fun i t => (L i x : ℂ) * fderiv ℝ f (t • x) (b i)) fun i _ => (continuous_const.mul (hc (b i))).intervalIntegrable _ _]`. Conclude with `Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _`.

Set `β : V → ℝ` to `fun x => 1 - q x * invCut (q x)`. Establish `hβs : ContDiff ℝ ∞ β` using `contDiff_const.sub (hqs.mul (contDiff_invCut.comp hqs))`. Establish `hβ0 : ∀ x, 1 ≤ q x → β x = 0`. Introduce `x hx`. Simplify using `only [β]`.

Rewrite using `[invCut_of_one_le hx, mul_inv_cancel₀ (by linarith), sub_self]`. Establish `hnorm : ∀ x, q x < 1 → ‖x‖ ≤ ∑ i, ‖b i‖`. Introduce `x hx`. Establish `hLi : ∀ i, |L i x| ≤ 1`. Introduce `i`.

Establish `: L i x ^ 2 ≤ q x` using `Finset.single_le_sum (f := fun j => L j x ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)`. Conclude with `(sq_le_one_iff_abs_le_one _).1 (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul, Real.norm_eq_abs]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hLi i)`.

Establish `hβc : HasCompactSupport (fun x => (β x : ℂ))`. Use `HasCompactSupport.intro (isCompact_closedBall (0 : V) (∑ i, ‖b i‖)) fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[Metric.mem_closedBall, dist_zero_right, not_le]`. Establish `: 1 ≤ q x`. Assume the negation of the conclusion as `h`.

Conclude with `absurd (hnorm x (not_le.1 h)) (not_le.2 hx)`. Rewrite using `[hβ0 x this, Complex.ofReal_zero]`. Establish `hnear : ∀ i, HasCompactSupport ((fun x => (β x : ℂ)) * k i)` using `fun i => hβc.mul_right`. Establish `hnears : ∀ i, ContDiff ℝ ∞ ((fun x => (β x : ℂ)) * k i)` using `fun i => (Complex.ofRealCLM.contDiff.comp hβs).mul (hk i)`. Set `a : Fin (Module.finrank ℝ V) → V → ℂ` to `fun i x => ((L i x * invCut (q x) : ℝ) : ℂ)`.

Establish `ha : ∀ i, (a i).HasTemperateGrowth` using `fun i => Function.Complex.hasTemperateGrowth_ofReal.comp ((L i).hasTemperateGrowth.mul (hasTemperateGrowth_invCut.comp hq))`. Establish `hLc : ∀ i, (fun x => (L i x : ℂ)).HasTemperateGrowth` using `fun i => Function.Complex.hasTemperateGrowth_ofReal.comp (L i).hasTemperateGrowth`. Set `h : Fin (Module.finrank ℝ V) → SchwartzMap V ℂ` to `fun i => (hnear i).toSchwartzMap (hnears i) + SchwartzMap.smulLeftCLM ℂ (a i) f`. Establish `hh : ∀ i x, h i x = (β x : ℂ) * k i x + a i x * f x`. Introduce `i x`.

Establish `e : ((hnear i).toSchwartzMap (hnears i) : V → ℂ) x = (β x : ℂ) * k i x` using `rfl`. Simplify using `only [h, SchwartzMap.add_apply, e, SchwartzMap.smulLeftCLM_apply_apply (ha i), smul_eq_mul]`. Use `⟨Module.finrank ℝ V, L, h, fun i => SchwartzMap.smulLeftCLM ℂ (fun x => (L i x : ℂ)) (h i), fun i x => by rw [SchwartzMap.smulLeftCLM_apply_apply (hLc i), smul_eq_mul], fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [SchwartzMap.smulLeftCLM_apply_apply (hLc _), smul_eq_mul, hh]`. Establish `e1 : ∀ i, (L i x : ℂ) * ((β x : ℂ) * k i x + a i x * f x) = (β x : ℂ) * ((L i x : ℂ) * k i x) + ((L i x ^ 2 * invCut (q x) : ℝ) : ℂ) * f x`.

Introduce `i`. Simplify using `only [a]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, ← Finset.mul_sum, ← key x, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_mul]`.

Simplify using `only [β, q]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hadamard (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (hf0 : f 0 = 0) :
    ∃ (n : ℕ) (L : Fin n → V →L[ℝ] ℝ) (h g : Fin n → SchwartzMap V ℂ),
      (∀ i x, g i x = (L i x : ℂ) * h i x) ∧ ∀ x, f x = ∑ i, g i x := by
  let b := Module.finBasis ℝ V
  let L : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hL : ∀ i x, L i x = b.repr x i := fun i x => by simp [L, Module.Basis.coord_apply]
  let q : V → ℝ := fun x => ∑ i, L i x ^ 2
  have hq : q.HasTemperateGrowth := by
    simp only [q]
    exact Function.HasTemperateGrowth.sum fun i _ => ((L i).hasTemperateGrowth).pow 2
  have hqs : ContDiff ℝ ∞ q := hq.1
  have hfs : ContDiff ℝ ∞ f := f.smooth ⊤
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hfs.fderiv_right (by simp)

  let k : Fin (Module.finrank ℝ V) → V → ℂ := fun i x => ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) (b i)
  have hk : ∀ i, ContDiff ℝ ∞ (k i) := by
    intro i
    have hΘ : ContDiff ℝ ∞ fun p : V × ℝ => fderiv ℝ f (p.2 • p.1) (b i) :=
      (hfd.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_const
    have key := contDiff_integral_smul_param (ν := volume.restrict (Ioc (0 : ℝ) 1)) (c := id)
      (S := Icc (0 : ℝ) 1) (φ := fun _ => (1 : ℂ)) aestronglyMeasurable_id isCompact_Icc
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => Ioc_subset_Icc_self ht)
      (integrableOn_const (by simp)) hΘ
    convert key using 2 with x
    simp [k, intervalIntegral.integral_of_le zero_le_one]
  have key : ∀ x, f x = ∑ i, (L i x : ℂ) * k i x := by
    intro x
    have hc : ∀ v : V, Continuous fun t : ℝ => fderiv ℝ f (t • x) v := fun v =>
      (hfd.continuous.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
    have h1 : ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) x = f ((1 : ℝ) • x) - f ((0 : ℝ) • x) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => f (t • x)) (fun t _ => ?_)
        ((hc x).intervalIntegrable _ _)
      have := (f.differentiableAt (x := t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
      simp only [one_smul] at this
      exact this
    rw [one_smul, zero_smul, hf0, sub_zero] at h1
    rw [← h1]
    have h2 : ∀ t : ℝ, fderiv ℝ f (t • x) x = ∑ i, (L i x : ℂ) * fderiv ℝ f (t • x) (b i) := by
      intro t
      rw [show fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ i, b.repr x i • b i) by rw [b.sum_repr], map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Complex.real_smul, hL]
    simp_rw [h2]
    rw [intervalIntegral.integral_finset_sum (f := fun i t => (L i x : ℂ) * fderiv ℝ f (t • x) (b i))
      fun i _ => (continuous_const.mul (hc (b i))).intervalIntegrable _ _]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _

  let β : V → ℝ := fun x => 1 - q x * invCut (q x)
  have hβs : ContDiff ℝ ∞ β := contDiff_const.sub (hqs.mul (contDiff_invCut.comp hqs))
  have hβ0 : ∀ x, 1 ≤ q x → β x = 0 := by
    intro x hx
    simp only [β]
    rw [invCut_of_one_le hx, mul_inv_cancel₀ (by linarith), sub_self]
  have hnorm : ∀ x, q x < 1 → ‖x‖ ≤ ∑ i, ‖b i‖ := by
    intro x hx
    have hLi : ∀ i, |L i x| ≤ 1 := by
      intro i
      have : L i x ^ 2 ≤ q x :=
        Finset.single_le_sum (f := fun j => L j x ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      exact (sq_le_one_iff_abs_le_one _).1 (by linarith)
    calc ‖x‖ = ‖∑ i, L i x • b i‖ := by simp only [hL, b.sum_repr]
      _ ≤ ∑ i, ‖L i x • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (hLi i)
  have hβc : HasCompactSupport (fun x => (β x : ℂ)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V) (∑ i, ‖b i‖)) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    have : 1 ≤ q x := by
      by_contra h
      exact absurd (hnorm x (not_le.1 h)) (not_le.2 hx)
    rw [hβ0 x this, Complex.ofReal_zero]
  have hnear : ∀ i, HasCompactSupport ((fun x => (β x : ℂ)) * k i) := fun i => hβc.mul_right
  have hnears : ∀ i, ContDiff ℝ ∞ ((fun x => (β x : ℂ)) * k i) := fun i =>
    (Complex.ofRealCLM.contDiff.comp hβs).mul (hk i)

  let a : Fin (Module.finrank ℝ V) → V → ℂ := fun i x => ((L i x * invCut (q x) : ℝ) : ℂ)
  have ha : ∀ i, (a i).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp ((L i).hasTemperateGrowth.mul (hasTemperateGrowth_invCut.comp hq))
  have hLc : ∀ i, (fun x => (L i x : ℂ)).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp (L i).hasTemperateGrowth
  let h : Fin (Module.finrank ℝ V) → SchwartzMap V ℂ := fun i =>
    (hnear i).toSchwartzMap (hnears i) + SchwartzMap.smulLeftCLM ℂ (a i) f
  have hh : ∀ i x, h i x = (β x : ℂ) * k i x + a i x * f x := by
    intro i x
    have e : ((hnear i).toSchwartzMap (hnears i) : V → ℂ) x = (β x : ℂ) * k i x := rfl
    simp only [h, SchwartzMap.add_apply, e, SchwartzMap.smulLeftCLM_apply_apply (ha i), smul_eq_mul]
  refine ⟨Module.finrank ℝ V, L, h, fun i => SchwartzMap.smulLeftCLM ℂ (fun x => (L i x : ℂ)) (h i),
    fun i x => by rw [SchwartzMap.smulLeftCLM_apply_apply (hLc i), smul_eq_mul], fun x => ?_⟩
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hLc _), smul_eq_mul, hh]
  have e1 : ∀ i, (L i x : ℂ) * ((β x : ℂ) * k i x + a i x * f x) =
      (β x : ℂ) * ((L i x : ℂ) * k i x) + ((L i x ^ 2 * invCut (q x) : ℝ) : ℂ) * f x := by
    intro i; simp only [a]; push_cast; ring
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, ← Finset.mul_sum, ← key x,
    ← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_mul]
  simp only [β, q]
  push_cast
  ring

end GlobalTheory.SchwartzDiv
