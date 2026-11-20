import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MulVecEqZeroOfPair

open Filter Topology Matrix

namespace GlobalTheory.CompanionTheory.PeriodLimitSeq

open GlobalTheory.CompanionTheory.PeriodLimit

/- English proof (translation)
Take `⟨M, hM⟩` from `Metric.tendsto_atTop.1 h (1 / 2) (by norm_num)`. Establish `key : ∀ m ≥ M, a m = a M`. Introduce `m hm`. Establish `h2 : dist (a m : ℂ) (a M : ℂ) < 1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `h2` using `[Complex.dist_eq, ← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs]`. Establish `h3 : |a m - a M| < 1` using `by exact_mod_cast h2`. Conclude with `sub_eq_zero.1 (Int.abs_lt_one_iff.1 h3)`. Establish `hev : ∀ᶠ m in atTop, a m = a M` using `eventually_atTop.2 ⟨M, key⟩`. Use `⟨a M, ?_, hev⟩` and prove the remaining obligations.

Conclude with `tendsto_nhds_unique h (tendsto_const_nhds.congr' (hev.mono fun m hm => by simp [hm]))`.
-/
theorem int_seq_const (a : ℕ → ℤ) (L : ℂ) (h : Tendsto (fun m => (a m : ℂ)) atTop (𝓝 L)) :
    ∃ N : ℤ, L = N ∧ ∀ᶠ m in atTop, a m = N := by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 h (1 / 2) (by norm_num)
  have key : ∀ m ≥ M, a m = a M := by
    intro m hm
    have h2 : dist (a m : ℂ) (a M : ℂ) < 1 := by
      calc dist (a m : ℂ) (a M : ℂ) ≤ dist (a m : ℂ) L + dist (a M : ℂ) L :=
            dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add (hM m hm) (hM M le_rfl)
        _ = 1 := by norm_num
    rw [Complex.dist_eq, ← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs] at h2
    have h3 : |a m - a M| < 1 := by exact_mod_cast h2
    exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 h3)
  have hev : ∀ᶠ m in atTop, a m = a M := eventually_atTop.2 ⟨M, key⟩
  refine ⟨a M, ?_, hev⟩
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (hev.mono fun m hm => by simp [hm]))

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem mulVec_expand {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (A : Matrix (Fin g) (Fin g) ℂ)
    (t : ℂ) (v : Fin g → ℤ) (k : Fin g) :
    ((A + t • Bs.map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k
      = (A *ᵥ (fun k => (v k : ℂ))) k + t * (((Bs *ᵥ v) k : ℤ) : ℂ) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]`.
-/
private theorem im_mulVec_lemma {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) (k : Fin g) :
    ((M *ᵥ (fun k => (v k : ℂ))) k).im = ((M.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

/- English proof (translation)
Establish `hyk : ∀ k, Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k) atTop (𝓝 (y k))` using `fun k => tendsto_pi_nhds.1 hy k`. Establish `hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (v k : ℂ))) k) atTop (𝓝 ((σ *ᵥ (fun k => (v k : ℂ))) k))`. Introduce `k`. Establish `hc : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (v k : ℂ))) k)` using `(continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)`. Conclude with `(hc.tendsto σ).comp hσ`.

Establish `htpos : ∀ᶠ m in atTop, 0 < (t m).im` using `ht.eventually_gt_atTop 0`. Establish `hid : ∀ m, vs m = v → ∀ k, (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im + (t m).im * (((Bs *ᵥ v) k : ℤ) : ℝ)`. Introduce `m hm k`. Rewrite using `[Pi.add_apply, hm, hτ m, mulVec_expand]`. Simplify using `[Complex.mul_im]`.

Establish `hker : Bs *ᵥ v = 0`. Use function extensionality and compare the values at `k`. Establish `hf : Tendsto (fun m => ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im) atTop (𝓝 0)` using `(((Complex.continuous_im.tendsto _).comp (hyk k)).sub ((Complex.continuous_im.tendsto _).comp (hσk k))).div_atTop ht`. Establish `hfreq : ∃ᶠ m in atTop, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im = (((Bs *ᵥ v) k : ℤ) : ℝ)`. Use `(hv.and_eventually htpos).mono fun m hm => ?_` and prove the remaining obligations.

Rewrite using `[hid m hm.1 k, add_sub_cancel_left]`. Conclude with `mul_div_cancel_left₀ _ hm.2.ne'`. Establish `h0` using `tendsto_nhds_unique_of_frequently_eq hf tendsto_const_nhds hfreq`. Use `show (Bs *ᵥ v) k = 0`. Conclude with `h0.symm` after adjusting the coercions.

Use `⟨hker, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← im_mulVec_lemma σ v k]`. Establish `hfreq2 : ∃ᶠ m in atTop, (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im`. Use `hv.mono fun m hm => ?_` and prove the remaining obligations. Rewrite using `[hid m hm k, hker]`.

Simplify using the standard rewrite rules. Conclude with `tendsto_nhds_unique_of_frequently_eq ((Complex.continuous_im.tendsto _).comp (hyk k)) ((Complex.continuous_im.tendsto _).comp (hσk k)) hfreq2`.
-/
theorem freq_ker {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ)
    (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ)
    (hσ : Tendsto σs atTop (𝓝 σ)) (ht : Tendsto (fun m => (t m).im) atTop atTop)
    (hτ : ∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ)))
    (hy : Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y))
    (v : Fin g → ℤ) (hv : ∃ᶠ m in atTop, vs m = v) :
    Bs *ᵥ v = 0 ∧ ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k := by
  have hyk : ∀ k, Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k)
      atTop (𝓝 (y k)) := fun k => tendsto_pi_nhds.1 hy k
  have hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (v k : ℂ))) k) atTop
      (𝓝 ((σ *ᵥ (fun k => (v k : ℂ))) k)) := by
    intro k
    have hc : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (v k : ℂ))) k) :=
      (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
    exact (hc.tendsto σ).comp hσ
  have htpos : ∀ᶠ m in atTop, 0 < (t m).im := ht.eventually_gt_atTop 0
  have hid : ∀ m, vs m = v → ∀ k,
      (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im + (t m).im * (((Bs *ᵥ v) k : ℤ) : ℝ) := by
    intro m hm k
    rw [Pi.add_apply, hm, hτ m, mulVec_expand]
    simp [Complex.mul_im]
  have hker : Bs *ᵥ v = 0 := by
    funext k
    have hf : Tendsto (fun m => ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im) atTop (𝓝 0) :=
      (((Complex.continuous_im.tendsto _).comp (hyk k)).sub
        ((Complex.continuous_im.tendsto _).comp (hσk k))).div_atTop ht
    have hfreq : ∃ᶠ m in atTop, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im = (((Bs *ᵥ v) k : ℤ) : ℝ) := by
      refine (hv.and_eventually htpos).mono fun m hm => ?_
      rw [hid m hm.1 k, add_sub_cancel_left]
      exact mul_div_cancel_left₀ _ hm.2.ne'
    have h0 := tendsto_nhds_unique_of_frequently_eq hf tendsto_const_nhds hfreq
    show (Bs *ᵥ v) k = 0
    exact_mod_cast h0.symm
  refine ⟨hker, fun k => ?_⟩
  rw [← im_mulVec_lemma σ v k]
  have hfreq2 : ∃ᶠ m in atTop,
      (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im := by
    refine hv.mono fun m hm => ?_
    rw [hid m hm k, hker]
    simp
  exact tendsto_nhds_unique_of_frequently_eq ((Complex.continuous_im.tendsto _).comp (hyk k))
    ((Complex.continuous_im.tendsto _).comp (hσk k)) hfreq2

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
private theorem cast_mulVec_lemma_2 {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ (fun k => (v k : ℝ)) = fun k => (((Bs *ᵥ v) k : ℤ) : ℝ) := by
  funext k
  simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Take `⟨w, hw⟩ : ∃ w : Fin g → ℝ, w = (fun k => (v k : ℝ)) - (fun k => (v' k : ℝ))` from `⟨_, rfl⟩`. Establish `hBw : Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ w = 0`. Rewrite using `[hw, Matrix.mulVec_sub, cast_mulVec_lemma_2, cast_mulVec_lemma_2, hk, hk']`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Establish `hSw : (σ.map Complex.im) *ᵥ w = 0`. Use function extensionality and compare the values at `k`. Establish `e1` using `hi k`. Establish `e2` using `hi' k`. Rewrite using `[hw, Matrix.mulVec_sub, Pi.sub_apply, Pi.zero_apply, ← e1, ← e2, sub_self]`.

Establish `h1` using `hpos w hBw`. Rewrite `h1` using `[hSw, dotProduct_zero]`. Establish `h3 : 0 ≤ w ⬝ᵥ w` using `Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)`. Establish `h5 : w ⬝ᵥ w ≤ 0`. Assume the negation of the conclusion as `hne`.

Use `mul_pos hc (not_le.1 hne)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : w = 0` using `dotProduct_self_eq_zero.1 (le_antisymm h5 h3)`. Use function extensionality and compare the values at `k`. Establish `h6` using `congrFun h4 k`.

Rewrite `h6` using `[hw]`. Simplify using `only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h6`. Conclude with `h6` after adjusting the coercions.
-/
theorem unique_value {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ)
    (c : ℝ) (hc : 0 < c) (y : Fin g → ℂ)
    (hpos : ∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 →
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v))
    (v v' : Fin g → ℤ) (hk : Bs *ᵥ v = 0) (hk' : Bs *ᵥ v' = 0)
    (hi : ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k)
    (hi' : ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v' k : ℝ))) k) : v = v' := by
  obtain ⟨w, hw⟩ : ∃ w : Fin g → ℝ, w = (fun k => (v k : ℝ)) - (fun k => (v' k : ℝ)) := ⟨_, rfl⟩
  have hBw : Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, cast_mulVec_lemma_2, cast_mulVec_lemma_2, hk, hk']
    funext k
    simp
  have hSw : (σ.map Complex.im) *ᵥ w = 0 := by
    funext k
    have e1 := hi k
    have e2 := hi' k
    rw [hw, Matrix.mulVec_sub, Pi.sub_apply, Pi.zero_apply, ← e1, ← e2, sub_self]
  have h1 := hpos w hBw
  rw [hSw, dotProduct_zero] at h1
  have h3 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
  have h5 : w ⬝ᵥ w ≤ 0 := by
    by_contra hne
    have := mul_pos hc (not_le.1 hne)
    linarith
  have h4 : w = 0 := dotProduct_self_eq_zero.1 (le_antisymm h5 h3)
  funext k
  have h6 := congrFun h4 k
  rw [hw] at h6
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h6
  exact_mod_cast h6

/- English proof (translation)
Introduce `g Bs σ σs τs t c us vs y hc hσ ht hτ hpsd hposσ hy`. Establish `huniq : ∀ w w' : Fin g → ℤ, (∃ᶠ m in atTop, vs m = w) → (∃ᶠ m in atTop, vs m = w') → w = w'`. Introduce `w w' hw hw'`. Take `⟨hk, hi⟩` from `freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w hw`. Take `⟨hk', hi'⟩` from `freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w' hw'`.

Conclude with `unique_value Bs σ c hc y hposσ w w' hk hk' hi hi'`. Establish `hS : Tendsto (fun m => ∑ k, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ)) : Fin g → ℂ)) k).im ^ 2) atTop (𝓝 (∑ k, (y k).im ^ 2))`. Use `tendsto_finsetSum _ fun k _ => ?_` and prove the remaining obligations. Conclude with `((Complex.continuous_im.tendsto _).comp (tendsto_pi_nhds.1 hy k)).pow 2`. Establish `hbd : ∀ᶠ m in atTop, vs m ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2}` using `by filter_upwards [hS.eventually_lt_const (lt_add_one _)] with m hm`.

Establish `h1` using `sq_mul_sum_sq_le ((τs m).map Complex.im) hc (hpsd m) (fun k => (vs m k : ℝ))`. Simplify using `only [im_period (τs m) (us m) (vs m)] at h1`. Use `show ∑ k, (vs m k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2`. Rewrite using `[le_div_iff₀ (pow_pos hc 2)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hfin` using `finite_sum_sq_le (g := g) ((∑ k, (y k).im ^ 2 + 1) / c ^ 2)`. Establish `hall : ∀ᶠ m in atTop, ∀ w ∈ {w ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2} | ¬ ∃ᶠ n in atTop, vs n = w}, vs m ≠ w`. Rewrite using `[Filter.eventually_all_finite (hfin.subset (Set.sep_subset _ _))]`. Introduce `w hw`. Conclude with `Filter.not_frequently.1 hw.2`.

Establish `hev : ∀ᶠ m in atTop, ∃ᶠ n in atTop, vs n = vs m` using `by filter_upwards [hbd, hall] with m hm1 hm2`. Assume the negation of the conclusion as `hne`. Conclude with `hm2 (vs m) ⟨hm1, hne⟩ rfl`. Take `⟨m0, hm0⟩` from `hev.exists`. Establish `hv_ev : ∀ᶠ m in atTop, vs m = vs m0` using `by filter_upwards [hev] with m hm`.

Conclude with `huniq _ _ hm hm0`. Take `⟨hker, -⟩` from `freq_ker Bs σ σs τs t us vs y hσ ht hτ hy (vs m0) hv_ev.frequently`. Establish `hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop (𝓝 ((σ *ᵥ (fun k => (vs m0 k : ℂ))) k))`. Introduce `k`. Establish `hc' : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (vs m0 k : ℂ))) k)` using `(continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)`.

Conclude with `(hc'.tendsto σ).comp hσ`. Establish `hu : ∀ k, Tendsto (fun m => (us m k : ℂ)) atTop (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k))`. Introduce `k`. Establish `h1 : Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k - (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k))` using `(tendsto_pi_nhds.1 hy k).sub (hσk k)`. Use `h1.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [hv_ev] with m hm`. Rewrite using `[Pi.add_apply, hm, hτ m, mulVec_expand, hker]`. Simplify using the standard rewrite rules. Use `choose u hu1 hu2 using fun k => int_seq_const (fun m => us m k) _ (hu k)`. Use `⟨u, vs m0, hker, ?_, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply]`. Rewrite using `[← hu1 k]`. Expand and normalize the polynomial expressions, which then agree. Establish `hall2 : ∀ᶠ m in atTop, ∀ k, us m k = u k` using `Filter.eventually_all.2 hu2 filter_upwards [hall2, hv_ev] with m h1 h2`.

Conclude with `⟨funext h1, h2⟩`.
-/
theorem limit_seq : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ) (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (c : ℝ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ), 0 < c → Tendsto σs atTop (𝓝 σ) → Tendsto (fun m => (t m).im) atTop atTop → (∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ))) → (∀ m, ((τs m).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v)) → Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y) → ∃ u v : Fin g → ℤ, Bs *ᵥ v = 0 ∧ y = (fun k => (u k : ℂ)) + σ *ᵥ (fun k => (v k : ℂ)) ∧ ∀ᶠ m in atTop, us m = u ∧ vs m = v := by
  intro g Bs σ σs τs t c us vs y hc hσ ht hτ hpsd hposσ hy
  have huniq : ∀ w w' : Fin g → ℤ, (∃ᶠ m in atTop, vs m = w) → (∃ᶠ m in atTop, vs m = w') →
      w = w' := by
    intro w w' hw hw'
    obtain ⟨hk, hi⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w hw
    obtain ⟨hk', hi'⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w' hw'
    exact unique_value Bs σ c hc y hposσ w w' hk hk' hi hi'
  have hS : Tendsto (fun m => ∑ k, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ)) :
      Fin g → ℂ)) k).im ^ 2) atTop (𝓝 (∑ k, (y k).im ^ 2)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    exact ((Complex.continuous_im.tendsto _).comp (tendsto_pi_nhds.1 hy k)).pow 2
  have hbd : ∀ᶠ m in atTop,
      vs m ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2} := by
    filter_upwards [hS.eventually_lt_const (lt_add_one _)] with m hm
    have h1 := sq_mul_sum_sq_le ((τs m).map Complex.im) hc (hpsd m) (fun k => (vs m k : ℝ))
    simp only [im_period (τs m) (us m) (vs m)] at h1
    show ∑ k, (vs m k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2
    rw [le_div_iff₀ (pow_pos hc 2)]
    linarith
  have hfin := finite_sum_sq_le (g := g) ((∑ k, (y k).im ^ 2 + 1) / c ^ 2)
  have hall : ∀ᶠ m in atTop, ∀ w ∈ {w ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤
      (∑ k, (y k).im ^ 2 + 1) / c ^ 2} | ¬ ∃ᶠ n in atTop, vs n = w}, vs m ≠ w := by
    rw [Filter.eventually_all_finite (hfin.subset (Set.sep_subset _ _))]
    intro w hw
    exact Filter.not_frequently.1 hw.2
  have hev : ∀ᶠ m in atTop, ∃ᶠ n in atTop, vs n = vs m := by
    filter_upwards [hbd, hall] with m hm1 hm2
    by_contra hne
    exact hm2 (vs m) ⟨hm1, hne⟩ rfl
  obtain ⟨m0, hm0⟩ := hev.exists
  have hv_ev : ∀ᶠ m in atTop, vs m = vs m0 := by
    filter_upwards [hev] with m hm
    exact huniq _ _ hm hm0
  obtain ⟨hker, -⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy (vs m0) hv_ev.frequently
  have hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop
      (𝓝 ((σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) := by
    intro k
    have hc' : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (vs m0 k : ℂ))) k) :=
      (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
    exact (hc'.tendsto σ).comp hσ
  have hu : ∀ k, Tendsto (fun m => (us m k : ℂ)) atTop
      (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) := by
    intro k
    have h1 : Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k
        - (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop
        (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) :=
      (tendsto_pi_nhds.1 hy k).sub (hσk k)
    refine h1.congr' ?_
    filter_upwards [hv_ev] with m hm
    rw [Pi.add_apply, hm, hτ m, mulVec_expand, hker]
    simp
  choose u hu1 hu2 using fun k => int_seq_const (fun m => us m k) _ (hu k)
  refine ⟨u, vs m0, hker, ?_, ?_⟩
  · funext k
    simp only [Pi.add_apply]
    rw [← hu1 k]
    ring
  · have hall2 : ∀ᶠ m in atTop, ∀ k, us m k = u k := Filter.eventually_all.2 hu2
    filter_upwards [hall2, hv_ev] with m h1 h2
    exact ⟨funext h1, h2⟩

end GlobalTheory.CompanionTheory.PeriodLimitSeq
