import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Establish `: CompleteSpace H'` using `hH'c.completeSpace_coe`. Use `set Pw : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) := fun c => H'.starProjection (w c) with hPw`. Establish `hPwm : ∀ c, Pw c ∈ H'` using `fun c => H'.starProjection_apply_mem (w c)`. Establish `horth : ∀ c, ∀ y ∈ H', inner ℂ (w c - Pw c) y = 0` using `fun c y hy => H'.starProjection_inner_eq_zero (w c) y hy`. Establish `hinnerP : ∀ c, ∀ y ∈ H', inner ℂ (w c) y = inner ℂ (Pw c) y` using `fun c y hy => by`.

Use `horth c y hy` as an intermediate fact. Rewrite `this` using `[inner_sub_left, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hpyth : ∀ c, ‖w c‖ ^ 2 = ‖Pw c‖ ^ 2 + ‖w c - Pw c‖ ^ 2` using `fun c => by`. Establish `h0 : inner ℂ (Pw c) (w c - Pw c) = 0`. Rewrite using `[← inner_conj_symm, horth c _ (hPwm c), map_zero]`.

Use `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Pw c) (w c - Pw c) h0` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Simplify using `only [sq]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL2 : ∀ f : Lp ℂ 2 μ, ‖f‖ ^ 2 = ∫ g, ‖(f : G → ℂ) g‖ ^ 2 ∂μ` using `fun f => by`.

Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def, ← integral_re (MeasureTheory.L2.integrable_inner f f)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Conclude with `inner_self_eq_norm_sq (𝕜 := ℂ) ((f : G → ℂ) g)`. Establish `hcomp : ∀ v ∈ H', ∀ c, ‖v c‖ ^ 2 = ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d'` using `fun v hv c => by`. Rewrite using `[hL2, ← hschur (Pw c) (hPwm c) v hv]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hrep v (hH'P hv) c] with g hg`. Rewrite using `[hg, hinnerP c _ (hH'st g v hv)]`. Establish `hkey : ∀ v ∈ H', ‖v‖ ^ 2 = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d'` using `fun v hv => by`. Establish `h` using `PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Lp ℂ 2 μ) v`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨v0, hv0, hne⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hH'0`. Establish `hsum : ∑ c, ‖Pw c‖ ^ 2 = d'`. Establish `h` using `hkey v0 hv0`. Establish `hn : ‖v0‖ ^ 2 ≠ 0` using `pow_ne_zero _ (norm_ne_zero_iff.mpr hne)`.

Clear denominators, using `at h` for the nonvanishing conditions. Use polynomial arithmetic with `[h, hn, sq_nonneg ‖v0‖]`. Use `⟨hsum ▸ Finset.sum_le_sum fun c _ => by rw [hpyth c]; nlinarith [sq_nonneg ‖w c - Pw c‖], fun heq => ?_⟩` and prove the remaining obligations. Establish `hwc : ∀ c, w c ∈ H'`. Establish `h0 : ∑ c, ‖w c - Pw c‖ ^ 2 = 0`.

Use `congrArg (fun t => t - d') heq` as an intermediate fact. Simplify using `only [sub_self] at this`. Rewrite using `[← this, ← hsum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [hpyth c]; ring`. Introduce `c`.

Use `(Finset.sum_eq_zero_iff_of_nonneg fun c _ => sq_nonneg ‖w c - Pw c‖).mp h0 c (Finset.mem_univ c)` as an intermediate fact. Establish `h1 : w c - Pw c = 0` using `norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)`. Rewrite using `[sub_eq_zero.mp h1]`. Conclude with `hPwm c`. Establish `hadj : ∀ g (a b : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), inner ℂ a (ρ g b) = inner ℂ (ρ g⁻¹ a) b` using `fun g a b => by`.

Set `L : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗᵢ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)` to `⟨(ρ g : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), hiso g⟩`. Establish `e : ρ g (ρ g⁻¹ a) = a`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]`. Both sides reduce to the same expression. Use `conv_lhs => rw [← e]`.

Conclude with `L.inner_map_map _ _`. Introduce `v hv`. Use `set u := v - H'.starProjection v with hu`. Establish `huP : u ∈ HP` using `HP.sub_mem hv (hH'P (H'.starProjection_apply_mem v))`. Establish `hu0 : ∀ c, ((u c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] 0` using `fun c => by filter_upwards [hrep u huP c] with g hg`.

Rewrite using `[hg, hadj, Pi.zero_apply]`. Use `H'.starProjection_inner_eq_zero v _ (hH'st g⁻¹ _ (hwc c))` as an intermediate fact. Rewrite using `[← inner_conj_symm, this, map_zero]`. Establish `hu' : u = 0`. Use `(WithLp.ofLp_injective 2).eq_iff.mp ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `c`. Conclude with `Lp.eq_zero_iff_ae_eq_zero.mpr (hu0 c)`. Establish `: v = H'.starProjection v` using `sub_eq_zero.mp hu'`. Rewrite using `[this]`. Conclude with `H'.starProjection_apply_mem v`.
-/
theorem tf_ge_abstract {n : ℕ} {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (HP H' : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))) (hH'c : IsClosed (H' : Set (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))))
    (hH'P : H' ≤ HP) (hH'st : ∀ g, ∀ v ∈ H', ρ g v ∈ H') (hH'0 : H' ≠ ⊥)
    (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (hrep : ∀ v ∈ HP, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v))
    {d' : ℝ} (hd' : 0 < d')
    (hschur : ∀ x ∈ H', ∀ v ∈ H', ∫ g, ‖inner ℂ x (ρ g v)‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖v‖ ^ 2 / d') :
    d' ≤ ∑ c, ‖w c‖ ^ 2 ∧ (∑ c, ‖w c‖ ^ 2 = d' → HP ≤ H') := by
  have : CompleteSpace H' := hH'c.completeSpace_coe
  set Pw : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) := fun c => H'.starProjection (w c) with hPw
  have hPwm : ∀ c, Pw c ∈ H' := fun c => H'.starProjection_apply_mem (w c)
  have horth : ∀ c, ∀ y ∈ H', inner ℂ (w c - Pw c) y = 0 := fun c y hy =>
    H'.starProjection_inner_eq_zero (w c) y hy
  have hinnerP : ∀ c, ∀ y ∈ H', inner ℂ (w c) y = inner ℂ (Pw c) y := fun c y hy => by
    have := horth c y hy
    rwa [inner_sub_left, sub_eq_zero] at this
  have hpyth : ∀ c, ‖w c‖ ^ 2 = ‖Pw c‖ ^ 2 + ‖w c - Pw c‖ ^ 2 := fun c => by
    have h0 : inner ℂ (Pw c) (w c - Pw c) = 0 := by
      rw [← inner_conj_symm, horth c _ (hPwm c), map_zero]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Pw c) (w c - Pw c) h0
    rw [add_sub_cancel] at this
    simp only [sq]; linarith
  have hL2 : ∀ f : Lp ℂ 2 μ, ‖f‖ ^ 2 = ∫ g, ‖(f : G → ℂ) g‖ ^ 2 ∂μ := fun f => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def,
      ← integral_re (MeasureTheory.L2.integrable_inner f f)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ((f : G → ℂ) g)
  have hcomp : ∀ v ∈ H', ∀ c, ‖v c‖ ^ 2 = ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := fun v hv c => by
    rw [hL2, ← hschur (Pw c) (hPwm c) v hv]
    refine integral_congr_ae ?_
    filter_upwards [hrep v (hH'P hv) c] with g hg
    rw [hg, hinnerP c _ (hH'st g v hv)]
  have hkey : ∀ v ∈ H', ‖v‖ ^ 2 = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := fun v hv => by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Lp ℂ 2 μ) v
    calc ‖v‖ ^ 2 = ∑ c, ‖v c‖ ^ 2 := h
      _ = ∑ c, ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := Finset.sum_congr rfl fun c _ => hcomp v hv c
      _ = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := by rw [Finset.sum_mul, Finset.sum_div]
  obtain ⟨v0, hv0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH'0
  have hsum : ∑ c, ‖Pw c‖ ^ 2 = d' := by
    have h := hkey v0 hv0
    have hn : ‖v0‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
    field_simp at h
    nlinarith [h, hn, sq_nonneg ‖v0‖]
  refine ⟨hsum ▸ Finset.sum_le_sum fun c _ => by rw [hpyth c]; nlinarith [sq_nonneg ‖w c - Pw c‖], fun heq => ?_⟩
  have hwc : ∀ c, w c ∈ H' := by
    have h0 : ∑ c, ‖w c - Pw c‖ ^ 2 = 0 := by
      have := congrArg (fun t => t - d') heq
      simp only [sub_self] at this
      rw [← this, ← hsum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [hpyth c]; ring
    intro c
    have := (Finset.sum_eq_zero_iff_of_nonneg fun c _ => sq_nonneg ‖w c - Pw c‖).mp h0 c (Finset.mem_univ c)
    have h1 : w c - Pw c = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    rw [sub_eq_zero.mp h1]; exact hPwm c
  have hadj : ∀ g (a b : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), inner ℂ a (ρ g b) = inner ℂ (ρ g⁻¹ a) b := fun g a b => by
    let L : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗᵢ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) :=
      ⟨(ρ g : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), hiso g⟩
    have e : ρ g (ρ g⁻¹ a) = a := by
      rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
    conv_lhs => rw [← e]
    exact L.inner_map_map _ _
  intro v hv
  set u := v - H'.starProjection v with hu
  have huP : u ∈ HP := HP.sub_mem hv (hH'P (H'.starProjection_apply_mem v))
  have hu0 : ∀ c, ((u c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] 0 := fun c => by
    filter_upwards [hrep u huP c] with g hg
    rw [hg, hadj, Pi.zero_apply]
    have := H'.starProjection_inner_eq_zero v _ (hH'st g⁻¹ _ (hwc c))
    rw [← inner_conj_symm, this, map_zero]
  have hu' : u = 0 := by
    refine (WithLp.ofLp_injective 2).eq_iff.mp ?_
    funext c
    exact Lp.eq_zero_iff_ae_eq_zero.mpr (hu0 c)
  have : v = H'.starProjection v := sub_eq_zero.mp hu'
  rw [this]; exact H'.starProjection_apply_mem v

end ReciprocityTheory.ChartRestriction.DS
