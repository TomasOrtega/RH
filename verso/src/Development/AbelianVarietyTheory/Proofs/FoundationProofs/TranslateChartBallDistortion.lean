import Mathlib
open MeasureTheory Filter Topology Metric Set

namespace GlobalTheory

/- English proof (translation)
Use `set ε : ℝ := (κ - 1) / (2 * (3 + 2 * κ)) with hε`. Establish `hε0 : 0 < ε` using `div_pos (by linarith) (by linarith)`. Establish `hε1 : ε < 1 / 4`. Rewrite using `[hε, div_lt_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hκε : (1 + ε) ^ 2 < κ * (1 - ε) ^ 2`. Establish `h3 : ε * (3 + 2 * κ) = (κ - 1) / 2`. Rewrite using `[hε]`. Clear the denominators using the available nonvanishing facts. Use polynomial arithmetic with `[mul_pos (sub_pos.mpr hκ) (mul_pos hε0 hε0)]`.

Take `⟨η, hη0, hη⟩` from `Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε0)`. Establish `hD : ∀ a b : V, ‖a‖ < η → ‖b‖ < η → ‖m (e a) - m (e b) - ι (a - b)‖ ≤ ε * ‖a - b‖`. Introduce `a b ha hb`. Establish `h` using `@hη (a, b) (by`. Simplify using `only [Prod.dist_eq, dist_zero_right]`.

Conclude with `max_lt ha hb)`. Simplify using `using h`. Establish `hLc : ContinuousAt (fun x => L (e x)) 0` using `hL.comp_of_eq he.continuousAt he0`. Take `⟨η2, hη20, hη2⟩` from `Metric.continuousAt_iff.mp hLc ε hε0`. Establish `hLx : ∀ x : V, ‖x‖ < η2 → ∀ v : M, ‖L (e x) v - v‖ ≤ ε * ‖v‖`.

Introduce `x hx v`. Establish `h1` using `hη2 (by rwa [dist_zero_right] : dist x 0 < η2)`. Simplify using `only [he0, hL1, dist_eq_norm] at h1`. Establish `h2` using `(L (e x) - ContinuousLinearMap.id ℝ M).le_opNorm v`. Simplify using `only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at h2`.

Conclude with `h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg v))`. Establish `hU : e '' ball 0 η ∈ 𝓝 (1 : G)` using `hopen η hη0`. Establish `hφ : Continuous (fun p : V × V => e p.1 * e p.2)` using `(he.comp continuous_fst).mul (he.comp continuous_snd)`. Establish `hψ : Continuous (fun p : V × V => (e p.1)⁻¹ * e p.2)` using `(he.comp continuous_fst).inv.mul (he.comp continuous_snd)`. Establish `hφU : (fun p : V × V => e p.1 * e p.2) ⁻¹' (e '' ball 0 η) ∈ 𝓝 ((0 : V), (0 : V))` using `hφ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)`.

Establish `hψU : (fun p : V × V => (e p.1)⁻¹ * e p.2) ⁻¹' (e '' ball 0 η) ∈ 𝓝 ((0 : V), (0 : V))` using `hψ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)`. Take `⟨η3, hη30, hη3⟩` from `Metric.mem_nhds_iff.mp hφU`. Take `⟨η4, hη40, hη4⟩` from `Metric.mem_nhds_iff.mp hψU`. Establish `hφ' : ∀ a b : V, ‖a‖ < η3 → ‖b‖ < η3 → ∃ z, ‖z‖ < η ∧ e z = e a * e b`. Introduce `a b ha hb`.

Establish `hab : (a, b) ∈ ball ((0 : V), (0 : V)) η3`. Rewrite using `[mem_ball, Prod.dist_eq]`. Simplify using `only [dist_zero_right]`. Conclude with `max_lt ha hb`. Take `⟨z, hz, hze⟩` from `hη3 hab`.

Conclude with `⟨z, mem_ball_zero_iff.mp hz, hze⟩`. Establish `hψ' : ∀ a b : V, ‖a‖ < η4 → ‖b‖ < η4 → ∃ z, ‖z‖ < η ∧ e z = (e a)⁻¹ * e b`. Introduce `a b ha hb`. Establish `hab : (a, b) ∈ ball ((0 : V), (0 : V)) η4`. Rewrite using `[mem_ball, Prod.dist_eq]`.

Simplify using `only [dist_zero_right]`. Conclude with `max_lt ha hb`. Take `⟨z, hz, hze⟩` from `hη4 hab`. Conclude with `⟨z, mem_ball_zero_iff.mp hz, hze⟩`. Establish `h0η : ‖(0 : V)‖ < η` using `by simpa using hη0`.

Use `⟨min (η / 2) (min η2 (min (η3 / 2) (η4 / 2))), lt_min (by linarith) (lt_min hη20 (lt_min (by linarith) (by linarith))), ?_⟩` and prove the remaining obligations. Introduce `x hx r hr`. Rewrite `hx` using `[mem_ball_zero_iff]`. Take `⟨hr0, hrδ⟩` from `hr`. Establish `b1 : ‖x‖ < η / 2` using `lt_of_lt_of_le hx (min_le_left _ _)`.

Establish `b2 : ‖x‖ < η2` using `lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))`. Establish `b3 : ‖x‖ < η3 / 2` using `lt_of_lt_of_le hx ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))`. Establish `b4 : ‖x‖ < η4 / 2` using `lt_of_lt_of_le hx ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))`. Establish `r1 : r < η / 2` using `lt_of_lt_of_le hrδ (min_le_left _ _)`. Establish `r3 : r < η3 / 2` using `lt_of_lt_of_le hrδ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))`.

Establish `r4 : r < η4 / 2` using `lt_of_lt_of_le hrδ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))`. Establish `hmx : ∀ y, m (e x * e y) - m (e x) = L (e x) (m (e y) - m (e 0))`. Introduce `y`. Rewrite using `[map_sub, he0, ← hm, ← hm, mul_one]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `_ ⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Rewrite `hy` using `[mem_ball_zero_iff]`. Take `⟨z, hz, hze⟩` from `hφ' x y (by linarith) (by linarith)`. Use `⟨z, ?_, hze⟩` and prove the remaining obligations. Rewrite using `[mem_ball, dist_eq_norm]`.

Establish `e1` using `hD z x hz (by linarith)`. Establish `e2` using `hD y 0 (by linarith) h0η`. Rewrite `e2` using `[sub_zero]`. Establish `e3` using `hLx x b2 (m (e y) - m (e 0))`. Rewrite `e1` using `[hze, hmx y]`.

Establish `nι : ‖ι (z - x)‖ = ‖z - x‖` using `ι.norm_map _`. Establish `nιy : ‖ι y‖ = ‖y‖` using `ι.norm_map _`. Use `set v := m (e y) - m (e 0) with hv`. Establish `t1 : ‖z - x‖ ≤ ‖L (e x) v‖ + ε * ‖z - x‖`. Establish `h` using `norm_sub_norm_le (ι (z - x)) (L (e x) v)`.

Establish `h' : ‖ι (z - x) - L (e x) v‖ = ‖L (e x) v - ι (z - x)‖` using `norm_sub_rev _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t2 : ‖L (e x) v‖ ≤ (1 + ε) * ‖v‖`. Establish `h` using `norm_sub_norm_le (L (e x) v) v`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `t3 : ‖v‖ ≤ (1 + ε) * ‖y‖`. Establish `h` using `norm_sub_norm_le v (ι y)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `k1 : (1 - ε) * ‖z - x‖ ≤ (1 + ε) ^ 2 * ‖y‖`. Use `mul_le_mul_of_nonneg_left t3 (by linarith : (0 : ℝ) ≤ 1 + ε)` as an intermediate fact.

Combine the linear relations using `only [t1, t2, this]`. Establish `k2 : (1 + ε) ^ 2 * ‖y‖ < (1 + ε) ^ 2 * r` using `mul_lt_mul_of_pos_left hy (by positivity)`. Establish `k3 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r` using `mul_lt_mul_of_pos_right hκε hr0`. Establish `k4 : κ * (1 - ε) ^ 2 * r ≤ κ * (1 - ε) * r`. Establish `h1 : (1 - ε) ^ 2 ≤ 1 - ε`.

Rewrite using `[sq]`. Conclude with `mul_le_of_le_one_left (by linarith) (by linarith)`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith)) hr0.le`. Establish `k5 : (1 - ε) * ‖z - x‖ < (1 - ε) * (κ * r)` using `by linarith only [k1, k2, k3, k4]`. Conclude with `lt_of_mul_lt_mul_left k5 (by linarith)`.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Rewrite `hw` using `[mem_ball, dist_eq_norm]`. Establish `hwx` using `norm_sub_norm_le w x`. Take `⟨y, hyη, hye⟩` from `hψ' x w (by linarith) (by linarith)`. Establish `hexy : e w = e x * e y` using `by rw [hye, mul_inv_cancel_left]`.

Use `⟨e y, ⟨y, ?_, rfl⟩, hexy.symm⟩` and prove the remaining obligations. Rewrite using `[mem_ball_zero_iff]`. Establish `e1` using `hD w x (by linarith) (by linarith)`. Establish `e2` using `hD y 0 hyη h0η`. Rewrite `e2` using `[sub_zero]`.

Establish `e3` using `hLx x b2 (m (e y) - m (e 0))`. Rewrite `e1` using `[hexy, hmx y]`. Establish `nι : ‖ι (w - x)‖ = ‖w - x‖` using `ι.norm_map _`. Establish `nιy : ‖ι y‖ = ‖y‖` using `ι.norm_map _`. Use `set v := m (e y) - m (e 0) with hv`.

Establish `s1 : ‖L (e x) v‖ ≤ (1 + ε) * ‖w - x‖`. Establish `h` using `norm_sub_norm_le (L (e x) v) (ι (w - x))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `s2 : (1 - ε) * ‖v‖ ≤ ‖L (e x) v‖`. Establish `h` using `norm_sub_norm_le v (L (e x) v)`.

Establish `h' : ‖v - L (e x) v‖ = ‖L (e x) v - v‖` using `norm_sub_rev _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `s3 : (1 - ε) * ‖y‖ ≤ ‖v‖`. Establish `h` using `norm_sub_norm_le (ι y) v`. Establish `h' : ‖ι y - v‖ = ‖v - ι y‖` using `norm_sub_rev _ _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `k1 : (1 - ε) ^ 2 * ‖y‖ ≤ (1 - ε) * ‖v‖`. Use `mul_le_mul_of_nonneg_left s3 (by linarith : (0 : ℝ) ≤ 1 - ε)` as an intermediate fact. Combine the linear relations using `only [this]`. Establish `k2 : (1 + ε) * ‖w - x‖ < (1 + ε) * r` using `mul_lt_mul_of_pos_left hw (by linarith)`.

Establish `k3 : (1 + ε) * r ≤ (1 + ε) ^ 2 * r`. Combine the linear relations using `only [mul_pos hε0 hr0, mul_pos (mul_pos hε0 hε0) hr0]`. Establish `k4 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r` using `mul_lt_mul_of_pos_right hκε hr0`. Establish `k5 : (1 - ε) ^ 2 * ‖y‖ < (1 - ε) ^ 2 * (κ * r)`. Combine the linear relations using `only [k1, s2, s1, k2, k3, k4]`.

Conclude with `lt_of_mul_lt_mul_left k5 (pow_pos (by linarith) 2).le`.
-/
theorem translate_chart_ball_distortion
    (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup M]
    [NormedSpace ℝ M] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (e : V → G)
    (m : G → M) (ι : V →ₗᵢ[ℝ] M) (L : G → M →L[ℝ] M) (he : Continuous e) (he0 : e 0 = 1)
    (hd : HasStrictFDerivAt (fun x => m (e x)) ι.toContinuousLinearMap 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h))
    (hopen : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) (κ : ℝ) (hκ : 1 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ball (0 : V) δ, ∀ r ∈ Ioo (0 : ℝ) δ,
      (fun g => e x * g) '' (e '' ball 0 r) ⊆ e '' ball x (κ * r) ∧
      e '' ball x r ⊆ (fun g => e x * g) '' (e '' ball 0 (κ * r)) := by
  set ε : ℝ := (κ - 1) / (2 * (3 + 2 * κ)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have hε1 : ε < 1 / 4 := by
    rw [hε, div_lt_iff₀ (by linarith)]
    linarith
  have hκε : (1 + ε) ^ 2 < κ * (1 - ε) ^ 2 := by
    have h3 : ε * (3 + 2 * κ) = (κ - 1) / 2 := by
      rw [hε]
      field_simp
    nlinarith [mul_pos (sub_pos.mpr hκ) (mul_pos hε0 hε0)]
  obtain ⟨η, hη0, hη⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε0)
  have hD : ∀ a b : V, ‖a‖ < η → ‖b‖ < η →
      ‖m (e a) - m (e b) - ι (a - b)‖ ≤ ε * ‖a - b‖ := by
    intro a b ha hb
    have h := @hη (a, b) (by
      simp only [Prod.dist_eq, dist_zero_right]
      exact max_lt ha hb)
    simpa using h
  have hLc : ContinuousAt (fun x => L (e x)) 0 := hL.comp_of_eq he.continuousAt he0
  obtain ⟨η2, hη20, hη2⟩ := Metric.continuousAt_iff.mp hLc ε hε0
  have hLx : ∀ x : V, ‖x‖ < η2 → ∀ v : M, ‖L (e x) v - v‖ ≤ ε * ‖v‖ := by
    intro x hx v
    have h1 := hη2 (by rwa [dist_zero_right] : dist x 0 < η2)
    simp only [he0, hL1, dist_eq_norm] at h1
    have h2 := (L (e x) - ContinuousLinearMap.id ℝ M).le_opNorm v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg v))
  have hU : e '' ball 0 η ∈ 𝓝 (1 : G) := hopen η hη0
  have hφ : Continuous (fun p : V × V => e p.1 * e p.2) :=
    (he.comp continuous_fst).mul (he.comp continuous_snd)
  have hψ : Continuous (fun p : V × V => (e p.1)⁻¹ * e p.2) :=
    (he.comp continuous_fst).inv.mul (he.comp continuous_snd)
  have hφU : (fun p : V × V => e p.1 * e p.2) ⁻¹' (e '' ball 0 η) ∈ 𝓝 ((0 : V), (0 : V)) :=
    hφ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  have hψU : (fun p : V × V => (e p.1)⁻¹ * e p.2) ⁻¹' (e '' ball 0 η) ∈
      𝓝 ((0 : V), (0 : V)) :=
    hψ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  obtain ⟨η3, hη30, hη3⟩ := Metric.mem_nhds_iff.mp hφU
  obtain ⟨η4, hη40, hη4⟩ := Metric.mem_nhds_iff.mp hψU
  have hφ' : ∀ a b : V, ‖a‖ < η3 → ‖b‖ < η3 → ∃ z, ‖z‖ < η ∧ e z = e a * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η3 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη3 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have hψ' : ∀ a b : V, ‖a‖ < η4 → ‖b‖ < η4 → ∃ z, ‖z‖ < η ∧ e z = (e a)⁻¹ * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η4 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη4 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have h0η : ‖(0 : V)‖ < η := by simpa using hη0
  refine ⟨min (η / 2) (min η2 (min (η3 / 2) (η4 / 2))),
    lt_min (by linarith) (lt_min hη20 (lt_min (by linarith) (by linarith))), ?_⟩
  intro x hx r hr
  rw [mem_ball_zero_iff] at hx
  obtain ⟨hr0, hrδ⟩ := hr
  have b1 : ‖x‖ < η / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have b2 : ‖x‖ < η2 := lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have b3 : ‖x‖ < η3 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have b4 : ‖x‖ < η4 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have r1 : r < η / 2 := lt_of_lt_of_le hrδ (min_le_left _ _)
  have r3 : r < η3 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have r4 : r < η4 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmx : ∀ y, m (e x * e y) - m (e x) = L (e x) (m (e y) - m (e 0)) := by
    intro y
    rw [map_sub, he0, ← hm, ← hm, mul_one]
  constructor
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [mem_ball_zero_iff] at hy
    obtain ⟨z, hz, hze⟩ := hφ' x y (by linarith) (by linarith)
    refine ⟨z, ?_, hze⟩
    rw [mem_ball, dist_eq_norm]
    have e1 := hD z x hz (by linarith)
    have e2 := hD y 0 (by linarith) h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hze, hmx y] at e1
    have nι : ‖ι (z - x)‖ = ‖z - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have t1 : ‖z - x‖ ≤ ‖L (e x) v‖ + ε * ‖z - x‖ := by
      have h := norm_sub_norm_le (ι (z - x)) (L (e x) v)
      have h' : ‖ι (z - x) - L (e x) v‖ = ‖L (e x) v - ι (z - x)‖ := norm_sub_rev _ _
      linarith
    have t2 : ‖L (e x) v‖ ≤ (1 + ε) * ‖v‖ := by
      have h := norm_sub_norm_le (L (e x) v) v
      linarith
    have t3 : ‖v‖ ≤ (1 + ε) * ‖y‖ := by
      have h := norm_sub_norm_le v (ι y)
      linarith
    have k1 : (1 - ε) * ‖z - x‖ ≤ (1 + ε) ^ 2 * ‖y‖ := by
      have := mul_le_mul_of_nonneg_left t3 (by linarith : (0 : ℝ) ≤ 1 + ε)
      linarith only [t1, t2, this]
    have k2 : (1 + ε) ^ 2 * ‖y‖ < (1 + ε) ^ 2 * r := mul_lt_mul_of_pos_left hy (by positivity)
    have k3 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k4 : κ * (1 - ε) ^ 2 * r ≤ κ * (1 - ε) * r := by
      have h1 : (1 - ε) ^ 2 ≤ 1 - ε := by
        rw [sq]
        exact mul_le_of_le_one_left (by linarith) (by linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith)) hr0.le
    have k5 : (1 - ε) * ‖z - x‖ < (1 - ε) * (κ * r) := by linarith only [k1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (by linarith)
  · rintro _ ⟨w, hw, rfl⟩
    rw [mem_ball, dist_eq_norm] at hw
    have hwx := norm_sub_norm_le w x
    obtain ⟨y, hyη, hye⟩ := hψ' x w (by linarith) (by linarith)
    have hexy : e w = e x * e y := by rw [hye, mul_inv_cancel_left]
    refine ⟨e y, ⟨y, ?_, rfl⟩, hexy.symm⟩
    rw [mem_ball_zero_iff]
    have e1 := hD w x (by linarith) (by linarith)
    have e2 := hD y 0 hyη h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hexy, hmx y] at e1
    have nι : ‖ι (w - x)‖ = ‖w - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have s1 : ‖L (e x) v‖ ≤ (1 + ε) * ‖w - x‖ := by
      have h := norm_sub_norm_le (L (e x) v) (ι (w - x))
      linarith
    have s2 : (1 - ε) * ‖v‖ ≤ ‖L (e x) v‖ := by
      have h := norm_sub_norm_le v (L (e x) v)
      have h' : ‖v - L (e x) v‖ = ‖L (e x) v - v‖ := norm_sub_rev _ _
      linarith
    have s3 : (1 - ε) * ‖y‖ ≤ ‖v‖ := by
      have h := norm_sub_norm_le (ι y) v
      have h' : ‖ι y - v‖ = ‖v - ι y‖ := norm_sub_rev _ _
      linarith
    have k1 : (1 - ε) ^ 2 * ‖y‖ ≤ (1 - ε) * ‖v‖ := by
      have := mul_le_mul_of_nonneg_left s3 (by linarith : (0 : ℝ) ≤ 1 - ε)
      linarith only [this]
    have k2 : (1 + ε) * ‖w - x‖ < (1 + ε) * r := mul_lt_mul_of_pos_left hw (by linarith)
    have k3 : (1 + ε) * r ≤ (1 + ε) ^ 2 * r := by
      linarith only [mul_pos hε0 hr0, mul_pos (mul_pos hε0 hε0) hr0]
    have k4 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k5 : (1 - ε) ^ 2 * ‖y‖ < (1 - ε) ^ 2 * (κ * r) := by
      linarith only [k1, s2, s1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (pow_pos (by linarith) 2).le

end GlobalTheory
