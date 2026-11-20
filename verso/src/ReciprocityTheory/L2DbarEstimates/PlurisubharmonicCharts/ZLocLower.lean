import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

/- English proof (translation)
Establish `hnT : n ≤ T` using `hnT'.le`. Establish `hK : 0 ≤ C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))` using `by positivity`. Break down `hd.eq_or_lt with h0 | hdpos` into its components or cases. Substitute `h0` using the available equality. Establish `hz : (0:ℝ) ^ (T - n) = 0` using `zero_pow (by omega)`.

Rewrite `hF` using `[hz, mul_zero]`. Establish `hF' : F = 0` using `le_antisymm (by simpa using hF) hF0`. Rewrite using `[hF', zero_mul, zero_mul]`. Check the signs of the components of the expression. Establish `hSpos : 0 < Ssq` using `lt_of_lt_of_le (by positivity) hS`.

Establish `h1 : Ssq ^ (-((T : ℝ) - 1 / 2)) ≤ (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2))` using `Real.rpow_le_rpow_of_nonpos (by positivity) hS (by`. Establish `: (1:ℝ) ≤ T` using `by exact_mod_cast (show 1 ≤ T by omega)`. Use the proof step `linarith)`. Establish `h2 : Wsq ^ (-(1 / 2 : ℝ)) ≤ m6 ^ (-(1 / 2 : ℝ))` using `Real.rpow_le_rpow_of_nonpos hm hW (by norm_num)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hW0 : 0 ≤ Wsq ^ (-(1 / 2 : ℝ))` using `Real.rpow_nonneg (hm.le.trans hW) _`. Establish `hS0 : 0 ≤ Ssq ^ (-((T : ℝ) - 1 / 2))` using `Real.rpow_nonneg hSpos.le _`. Use `gcongr`. Use `_ = (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) * d ^ (-2 * ((n : ℝ) - 1 / 2)) := by`. Establish `e1 : (d ^ (T - n)) ^ 2 = d ^ (2 * ((T : ℝ) - n))`.

Rewrite using `[← pow_mul, ← Real.rpow_natCast]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub hnT]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) = c ^ (-((T : ℝ) - 1 / 2)) * d ^ (-2 * ((T : ℝ) - 1 / 2))`.

Rewrite using `[Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hd]`. Use `push_cast`. Put the polynomial expressions in normal form. Establish `e3 : d ^ (2 * ((T : ℝ) - n)) * d ^ (-2 * ((T : ℝ) - 1 / 2)) = d ^ (-2 * ((n : ℝ) - 1 / 2))`. Rewrite using `[← Real.rpow_add hdpos]`.

Put the polynomial expressions in normal form. Rewrite using `[mul_pow, e1, e2]`. Rewrite using `[← e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem real_bound {d F Ssq Wsq C1 B2 c m6 : ℝ} {T n : ℕ} (hnT' : n < T) (hd : 0 ≤ d)
    (hF0 : 0 ≤ F) (hF : F ≤ (C1 * d ^ (T - n)) ^ 2 * B2) (hB2 : 0 ≤ B2) (hc : 0 < c)
    (hS : c * d ^ 2 ≤ Ssq) (hm : 0 < m6) (hW : m6 ≤ Wsq) :
    F * Ssq ^ (-((T : ℝ) - 1 / 2)) * Wsq ^ (-(1 / 2 : ℝ)) ≤
      (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) *
        d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
  have hnT : n ≤ T := hnT'.le
  have hK : 0 ≤ C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ)) := by positivity
  rcases hd.eq_or_lt with h0 | hdpos
  · subst h0
    have hz : (0:ℝ) ^ (T - n) = 0 := zero_pow (by omega)
    rw [hz, mul_zero] at hF
    have hF' : F = 0 := le_antisymm (by simpa using hF) hF0
    rw [hF', zero_mul, zero_mul]
    positivity
  · have hSpos : 0 < Ssq := lt_of_lt_of_le (by positivity) hS
    have h1 : Ssq ^ (-((T : ℝ) - 1 / 2)) ≤ (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hS (by
        have : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
        linarith)
    have h2 : Wsq ^ (-(1 / 2 : ℝ)) ≤ m6 ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hm hW (by norm_num)
    calc F * Ssq ^ (-((T : ℝ) - 1 / 2)) * Wsq ^ (-(1 / 2 : ℝ))
        ≤ ((C1 * d ^ (T - n)) ^ 2 * B2) * (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) *
            m6 ^ (-(1 / 2 : ℝ)) := by
          have hW0 : 0 ≤ Wsq ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (hm.le.trans hW) _
          have hS0 : 0 ≤ Ssq ^ (-((T : ℝ) - 1 / 2)) := Real.rpow_nonneg hSpos.le _
          gcongr
      _ = (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) *
            d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
          have e1 : (d ^ (T - n)) ^ 2 = d ^ (2 * ((T : ℝ) - n)) := by
            rw [← pow_mul, ← Real.rpow_natCast]
            congr 1
            push_cast [Nat.cast_sub hnT]
            ring
          have e2 : (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) =
              c ^ (-((T : ℝ) - 1 / 2)) * d ^ (-2 * ((T : ℝ) - 1 / 2)) := by
            rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hd]
            push_cast
            ring_nf
          have e3 : d ^ (2 * ((T : ℝ) - n)) * d ^ (-2 * ((T : ℝ) - 1 / 2)) =
              d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
            rw [← Real.rpow_add hdpos]; ring_nf
          rw [mul_pow, e1, e2]
          rw [← e3]
          ring

/- English proof (translation)
Unfold `sqn`. Rewrite using `[EuclideanSpace.norm_sq_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[A.nsq_eq_chart (hs k) hx]`. Simplify using `only [zLoc, PiLp.toLp_apply, (A.chart i).left_inv hx, norm_div, div_pow]`.

Establish `: ‖w0 i x‖ ^ 2 ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
theorem sqn_s_eq (A : WeightedAtlas n Y ι La) {L : La} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hs : ∀ k, A.IsSec L (s k)) {i : ι} {x : Y} (hx : x ∈ (A.chart i).source)
    (hw : w0 i x ≠ 0) :
    A.sqn L s x = ‖w0 i x‖ ^ 2 * Real.exp (-A.ph L i x) * ‖A.zLoc w0 s i (A.chart i x)‖ ^ 2 := by
  unfold sqn
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [A.nsq_eq_chart (hs k) hx]
  simp only [zLoc, PiLp.toLp_apply, (A.chart i).left_inv hx, norm_div, div_pow]
  have : ‖w0 i x‖ ^ 2 ≠ 0 := by positivity
  field_simp

/- English proof (translation)
Use `set i := A.pick P`. Use `set vP := A.chart i P`. Use `set zL := A.zLoc w0 s i`. Establish `hdet : (fderiv ℂ zL vP).det ≠ 0` using `hD.coord P hP`. Establish `: Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`.

Establish `hdiff : DifferentiableAt ℂ zL vP`. Assume the negation of the conclusion as `h`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[fderiv_zero_of_not_differentiableAt h]`. Use `show LinearMap.det ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) = 0`.

Rewrite using `[ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, finrank_euclideanSpace, Fintype.card_fin]`. Conclude with `zero_pow (by omega)`. Establish `hz0 : zL vP = 0`. Use extensionality with `k`. Simplify using `only [zL, zLoc, PiLp.toLp_apply, vP, (A.chart i).left_inv (A.mem_pick P)]`.

Rewrite using `[hP k]`. Simplify using the standard rewrite rules. Use `set D := fderiv ℂ zL vP`. Use `set E := (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv`. Choose the witnesses or unpack the hypotheses as in `⟨K0, hK0⟩ : ∃ K0 : ℝ, ∀ u, ‖u‖ ≤ K0 * ‖D u‖ := by`.

Use `⟨‖(E.symm : V n →L[ℂ] V n)‖, fun u => ?_⟩` and prove the remaining obligations. Establish `h` using `E.antilipschitz.le_mul_dist u 0`. Simplify using `only [dist_zero_right, map_zero] at h`. Conclude with `h`. Use `set K1 := max K0 1`.

Establish `hK1 : 0 < K1` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Establish `hlo` using `hdiff.hasFDerivAt.isLittleO`. Establish `hev` using `hlo.def (show (0:ℝ) < 1 / (2 * K1) by positivity)`. Use `⟨2 * K1, by positivity, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hev] with v hv`.

Rewrite `hv` using `[hz0, sub_zero]`. Establish `h1 : ‖v - vP‖ ≤ K1 * ‖D (v - vP)‖` using `(hK0 _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))`. Establish `h2 : ‖D (v - vP)‖ ≤ ‖zL v‖ + ‖zL v - D (v - vP)‖`. Use `norm_sub_le (zL v) (zL v - D (v - vP))` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Establish `h3 : K1 * (1 / (2 * K1) * ‖v - vP‖) = ‖v - vP‖ / 2` using `by field_simp`. Use polynomial arithmetic with `[norm_nonneg (zL v - D (v - vP)), norm_nonneg (zL v)]`.
-/
theorem zLoc_lower (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (hn : 1 ≤ n) {P : Y}
    (hP : P ∈ A.zeroSet s) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ v in 𝓝 (A.chart (A.pick P) P),
      ‖v - A.chart (A.pick P) P‖ ≤ K * ‖A.zLoc w0 s (A.pick P) v‖ := by
  set i := A.pick P
  set vP := A.chart i P
  set zL := A.zLoc w0 s i
  have hdet : (fderiv ℂ zL vP).det ≠ 0 := hD.coord P hP
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdiff : DifferentiableAt ℂ zL vP := by
    by_contra h
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt h]
    show LinearMap.det ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) = 0
    rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, finrank_euclideanSpace, Fintype.card_fin]
    exact zero_pow (by omega)
  have hz0 : zL vP = 0 := by
    ext k
    simp only [zL, zLoc, PiLp.toLp_apply, vP, (A.chart i).left_inv (A.mem_pick P)]
    rw [hP k]; simp
  set D := fderiv ℂ zL vP
  set E := (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, ∀ u, ‖u‖ ≤ K0 * ‖D u‖ := by
    refine ⟨‖(E.symm : V n →L[ℂ] V n)‖, fun u => ?_⟩
    have h := E.antilipschitz.le_mul_dist u 0
    simp only [dist_zero_right, map_zero] at h
    exact h
  set K1 := max K0 1
  have hK1 : 0 < K1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlo := hdiff.hasFDerivAt.isLittleO
  have hev := hlo.def (show (0:ℝ) < 1 / (2 * K1) by positivity)
  refine ⟨2 * K1, by positivity, ?_⟩
  filter_upwards [hev] with v hv
  rw [hz0, sub_zero] at hv
  have h1 : ‖v - vP‖ ≤ K1 * ‖D (v - vP)‖ :=
    (hK0 _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h2 : ‖D (v - vP)‖ ≤ ‖zL v‖ + ‖zL v - D (v - vP)‖ := by
    have := norm_sub_le (zL v) (zL v - D (v - vP))
    rwa [sub_sub_cancel] at this
  have h3 : K1 * (1 / (2 * K1) * ‖v - vP‖) = ‖v - vP‖ / 2 := by field_simp
  nlinarith [norm_nonneg (zL v - D (v - vP)), norm_nonneg (zL v)]

/- English proof (translation)
Use `set i := A.pick P with hi`. Use `set e := A.chart i with he`. Use `set vP := e P with hvP`. Establish `hPs : P ∈ e.source` using `A.mem_pick P`. Establish `hvt : vP ∈ e.target` using `e.map_source hPs`.

Establish `htn : e.target ∈ 𝓝 vP` using `e.open_target.mem_nhds hvt`. Establish `hsymm : ContinuousAt e.symm vP` using `e.continuousAt_symm hvt`. Establish `hsP : e.symm vP = P` using `e.left_inv hPs`. Establish `cph : ∀ la' : La, ContinuousAt (fun v => A.ph la' i (e.symm v)) vP` using `fun la' => (A.smooth_ph la' i).continuousOn.continuousAt htn`. Establish `cw0 : ContinuousAt (fun v => w0 i (e.symm v)) vP`.

Establish `h` using `(hD.isSection_denom.1 i).continuousOn`. Simplify using `only [Set.preimage_univ, Set.inter_univ] at h`. Conclude with `h.continuousAt htn`. Take `⟨C1, hC1⟩` from `hv`. Take `⟨K3, hK3pos, hK3⟩` from `A.zLoc_lower hD (by omega) hP`.

Use `set B2 := Real.exp (-A.ph la i P) + 1 with hB2`. Establish `hE2 : ∀ᶠ v in 𝓝 vP, Real.exp (-A.ph la i (e.symm v)) < B2`. Establish `hc : ContinuousAt (fun v => Real.exp (-A.ph la i (e.symm v))) vP` using `Real.continuous_exp.continuousAt.comp (cph la).neg`. Conclude with `hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))`. Use `set g4 : V n → ℝ := fun v => ‖w0 i (e.symm v)‖ ^ 2 * Real.exp (-A.ph L i (e.symm v)) with hg4`.

Establish `g4P : 0 < g4 vP`. Simplify using `only [g4, hsP]`. Use `hD.w0_ne P hP` as an intermediate fact. Check the signs of the components of the expression. Establish `hE4 : ∀ᶠ v in 𝓝 vP, g4 vP / 2 < g4 v` using `((cw0.norm.pow 2).mul (Real.continuous_exp.continuousAt.comp (cph L).neg)).eventually (eventually_gt_nhds (half_lt_self g4P))`.

Use `set g6 : V n → ℝ := fun v => A.sqn L w (e.symm v) with hg6`. Establish `g6P : 0 < g6 vP`. Simplify using `only [g6, hsP]`. Take `⟨k, hk⟩` from `hD.no_common_zero P`. Establish `h0 : 0 < A.nsq L (w k) P`.

Unfold `nsq`. Use `norm_pos_iff.2 hk` as an intermediate fact. Check the signs of the components of the expression. Conclude with `lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A.nsq L (w j) P) (fun j _ => A.nsq_nonneg L (w j) P) (Finset.mem_univ k))`. Establish `hE6 : ∀ᶠ v in 𝓝 vP, g6 vP / 2 < g6 v` using `((A.continuous_sqn hD.sec_w).continuousAt.comp hsymm).eventually (eventually_gt_nhds (half_lt_self g6P))`.

Use `set B7 := Real.exp (A.ph A.kap i P) + 1 with hB7`. Establish `hE7 : ∀ᶠ v in 𝓝 vP, Real.exp (A.ph A.kap i (e.symm v)) < B7`. Establish `hc : ContinuousAt (fun v => Real.exp (A.ph A.kap i (e.symm v))) vP` using `Real.continuous_exp.continuousAt.comp (cph A.kap)`. Conclude with `hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff_ball.1 ((show ∀ᶠ v in 𝓝 vP, v ∈ e.target from htn).and (hC1.and (hE2.and (hK3.and (hE4.and (hE6.and hE7))))))`.

Use `set r := min ε 1 with hr`. Use `set W := Metric.ball vP r with hW`. Establish `hWb : W ⊆ Metric.ball vP ε` using `Metric.ball_subset_ball (min_le_left _ _)`. Establish `hWt : W ⊆ e.target` using `fun v hv => (hball v (hWb hv)).1`. Establish `hUo : IsOpen (e.source ∩ e ⁻¹' W)` using `e.isOpen_inter_preimage Metric.isOpen_ball`.

Use `⟨e.source ∩ e ⁻¹' W, hUo, ⟨hPs, Metric.mem_ball_self (lt_min hε one_pos)⟩, ?_⟩` and prove the remaining obligations. Use `set c := (g4 vP / 2) / K3 ^ 2 with hc`. Establish `hcpos : 0 < c` using `by positivity`. Use `set m6 := g6 vP / 2 with hm6`. Establish `hm6pos : 0 < m6` using `by positivity`.

Use `set K := C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ)) with hK`. Establish `hB2pos : 0 < B2` using `by positivity`. Establish `hKnn : 0 ≤ K` using `by positivity`. Use `set ψ : V n → ℝ≥0∞ := fun v => ENNReal.ofReal ‖v - vP‖ ^ (-2 * ((n : ℝ) - 1 / 2)) with hψ`. Establish `hψc : Continuous ψ` using `ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp (continuous_norm.comp (continuous_id.sub continuous_const)))`.

Establish `hpt : ∀ x ∈ e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq la f x * A.sqn L s x ^ (-((T : ℝ) - 1 / 2)) * A.sqn L w x ^ (-(1 / 2 : ℝ))) ≤ ENNReal.ofReal K * ψ (e x)`. Introduce and unpack `x ⟨hxs, hxW⟩`. Take `⟨-, h1, h2, h3, h4, h6, -⟩` from `hball (e x) (hWb hxW)`. Establish `hx : e.symm (e x) = x` using `e.left_inv hxs`. Simplify using `only [g4, g6, hx] at h4 h6`.

Rewrite `h1`, `h2` using `[hx]`. Use `set d := ‖e x - vP‖ with hd`. Establish `hw0 : w0 i x ≠ 0`. Introduce `h`. Rewrite `h4` using `[h, norm_zero]`.

Establish `: g4 vP / 2 < 0` using `by simpa using h4`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS : c * d ^ 2 ≤ A.sqn L s x`. Rewrite using `[A.sqn_s_eq hD.sec_s hxs hw0]`. Use `set z := ‖A.zLoc w0 s i (e x)‖`.

Establish `hz : d ^ 2 ≤ K3 ^ 2 * z ^ 2`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) h3 2`. Establish `hc1 : c * d ^ 2 ≤ (g4 vP / 2) * z ^ 2`. Rewrite using `[hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`.

Use polynomial arithmetic with `[g4P]`. Conclude with `hc1.trans (mul_le_mul_of_nonneg_right h4.le (sq_nonneg _))`. Establish `hF : A.nsq la f x ≤ (C1 * d ^ (T - n)) ^ 2 * B2`. Rewrite using `[A.nsq_eq_chart hf hxs]`. Conclude with `mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2.le (Real.exp_pos _).le (sq_nonneg _)`.

Establish `hR` using `real_bound (T := T) (n := n) (by omega) (norm_nonneg _) (A.nsq_nonneg la f x) hF hB2pos.le hcpos hS hm6pos h6.le`. Combine the equalities or inequalities in the displayed calculation. Break down `(norm_nonneg (e x - vP)).eq_or_lt with h0 | hpos` into its components or cases. Rewrite `h0` using `[← hd]`. Rewrite using `[← h0, Real.zero_rpow (by`.

Establish `: (2:ℝ) ≤ n` using `by exact_mod_cast hn`. Use the proof step `linarith)]`. Simplify using the standard rewrite rules. Simplify using `only [ψ]`. Rewrite using `[ENNReal.ofReal_rpow_of_pos hpos]`.

Establish `hUm : MeasurableSet (e.source ∩ e ⁻¹' W)` using `hUo.measurableSet`. Combine the equalities or inequalities in the displayed calculation. Conclude with `A.lintegral_chart_le i P Metric.isOpen_ball hWt _ (fun v hv => ENNReal.ofReal_le_ofReal (hball v (hWb hv)).2.2.2.2.2.2.le) ψ hψc`. Use `_ < ⊤ := by`. Use `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)` and prove the remaining obligations.

Conclude with `lintegral_ball_rpow_lt_top hMVI (by omega) vP (min_le_right _ _) (by linarith)`.
-/
theorem local_int (A : WeightedAtlas n Y ι La) (hMVI : MVIntStatement n) (hn : 2 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {f : ι → Y → ℂ} (hf : A.IsSec la f) {T : ℕ}
    (hT : n + 1 ≤ T) {P : Y} (hP : P ∈ A.zeroSet s) (hv : A.VanishOrd f P (T - n)) :
    ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧
      ∫⁻ y in U, ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤ := by
  set i := A.pick P with hi
  set e := A.chart i with he
  set vP := e P with hvP
  have hPs : P ∈ e.source := A.mem_pick P
  have hvt : vP ∈ e.target := e.map_source hPs
  have htn : e.target ∈ 𝓝 vP := e.open_target.mem_nhds hvt
  have hsymm : ContinuousAt e.symm vP := e.continuousAt_symm hvt
  have hsP : e.symm vP = P := e.left_inv hPs
  have cph : ∀ la' : La, ContinuousAt (fun v => A.ph la' i (e.symm v)) vP := fun la' =>
    (A.smooth_ph la' i).continuousOn.continuousAt htn
  have cw0 : ContinuousAt (fun v => w0 i (e.symm v)) vP := by
    have h := (hD.isSection_denom.1 i).continuousOn
    simp only [Set.preimage_univ, Set.inter_univ] at h
    exact h.continuousAt htn
  obtain ⟨C1, hC1⟩ := hv
  obtain ⟨K3, hK3pos, hK3⟩ := A.zLoc_lower hD (by omega) hP
  set B2 := Real.exp (-A.ph la i P) + 1 with hB2
  have hE2 : ∀ᶠ v in 𝓝 vP, Real.exp (-A.ph la i (e.symm v)) < B2 := by
    have hc : ContinuousAt (fun v => Real.exp (-A.ph la i (e.symm v))) vP :=
      Real.continuous_exp.continuousAt.comp (cph la).neg
    exact hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))
  set g4 : V n → ℝ := fun v => ‖w0 i (e.symm v)‖ ^ 2 * Real.exp (-A.ph L i (e.symm v)) with hg4
  have g4P : 0 < g4 vP := by
    simp only [g4, hsP]
    have := hD.w0_ne P hP
    positivity
  have hE4 : ∀ᶠ v in 𝓝 vP, g4 vP / 2 < g4 v :=
    ((cw0.norm.pow 2).mul (Real.continuous_exp.continuousAt.comp (cph L).neg)).eventually
      (eventually_gt_nhds (half_lt_self g4P))
  set g6 : V n → ℝ := fun v => A.sqn L w (e.symm v) with hg6
  have g6P : 0 < g6 vP := by
    simp only [g6, hsP]
    obtain ⟨k, hk⟩ := hD.no_common_zero P
    have h0 : 0 < A.nsq L (w k) P := by
      unfold nsq
      have := norm_pos_iff.2 hk
      positivity
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A.nsq L (w j) P)
      (fun j _ => A.nsq_nonneg L (w j) P) (Finset.mem_univ k))
  have hE6 : ∀ᶠ v in 𝓝 vP, g6 vP / 2 < g6 v :=
    ((A.continuous_sqn hD.sec_w).continuousAt.comp hsymm).eventually
      (eventually_gt_nhds (half_lt_self g6P))
  set B7 := Real.exp (A.ph A.kap i P) + 1 with hB7
  have hE7 : ∀ᶠ v in 𝓝 vP, Real.exp (A.ph A.kap i (e.symm v)) < B7 := by
    have hc : ContinuousAt (fun v => Real.exp (A.ph A.kap i (e.symm v))) vP :=
      Real.continuous_exp.continuousAt.comp (cph A.kap)
    exact hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((show ∀ᶠ v in 𝓝 vP, v ∈ e.target from htn).and (hC1.and (hE2.and (hK3.and (hE4.and (hE6.and hE7))))))
  set r := min ε 1 with hr
  set W := Metric.ball vP r with hW
  have hWb : W ⊆ Metric.ball vP ε := Metric.ball_subset_ball (min_le_left _ _)
  have hWt : W ⊆ e.target := fun v hv => (hball v (hWb hv)).1
  have hUo : IsOpen (e.source ∩ e ⁻¹' W) := e.isOpen_inter_preimage Metric.isOpen_ball
  refine ⟨e.source ∩ e ⁻¹' W, hUo, ⟨hPs, Metric.mem_ball_self (lt_min hε one_pos)⟩, ?_⟩
  set c := (g4 vP / 2) / K3 ^ 2 with hc
  have hcpos : 0 < c := by positivity
  set m6 := g6 vP / 2 with hm6
  have hm6pos : 0 < m6 := by positivity
  set K := C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ)) with hK
  have hB2pos : 0 < B2 := by positivity
  have hKnn : 0 ≤ K := by positivity
  set ψ : V n → ℝ≥0∞ := fun v => ENNReal.ofReal ‖v - vP‖ ^ (-2 * ((n : ℝ) - 1 / 2)) with hψ
  have hψc : Continuous ψ :=
    ENNReal.continuous_rpow_const.comp
      (ENNReal.continuous_ofReal.comp (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hpt : ∀ x ∈ e.source ∩ e ⁻¹' W,
      ENNReal.ofReal (A.nsq la f x * A.sqn L s x ^ (-((T : ℝ) - 1 / 2)) *
        A.sqn L w x ^ (-(1 / 2 : ℝ))) ≤ ENNReal.ofReal K * ψ (e x) := by
    rintro x ⟨hxs, hxW⟩
    obtain ⟨-, h1, h2, h3, h4, h6, -⟩ := hball (e x) (hWb hxW)
    have hx : e.symm (e x) = x := e.left_inv hxs
    simp only [g4, g6, hx] at h4 h6
    rw [hx] at h1 h2
    set d := ‖e x - vP‖ with hd
    have hw0 : w0 i x ≠ 0 := by
      intro h
      rw [h, norm_zero] at h4
      have : g4 vP / 2 < 0 := by simpa using h4
      linarith
    have hS : c * d ^ 2 ≤ A.sqn L s x := by
      rw [A.sqn_s_eq hD.sec_s hxs hw0]
      set z := ‖A.zLoc w0 s i (e x)‖
      have hz : d ^ 2 ≤ K3 ^ 2 * z ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      have hc1 : c * d ^ 2 ≤ (g4 vP / 2) * z ^ 2 := by
        rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [g4P]
      exact hc1.trans (mul_le_mul_of_nonneg_right h4.le (sq_nonneg _))
    have hF : A.nsq la f x ≤ (C1 * d ^ (T - n)) ^ 2 * B2 := by
      rw [A.nsq_eq_chart hf hxs]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2.le (Real.exp_pos _).le
        (sq_nonneg _)
    have hR := real_bound (T := T) (n := n) (by omega) (norm_nonneg _) (A.nsq_nonneg la f x) hF
      hB2pos.le hcpos hS hm6pos h6.le
    calc ENNReal.ofReal (A.nsq la f x * A.sqn L s x ^ (-((T : ℝ) - 1 / 2)) *
          A.sqn L w x ^ (-(1 / 2 : ℝ)))
        ≤ ENNReal.ofReal (K * d ^ (-2 * ((n : ℝ) - 1 / 2))) := ENNReal.ofReal_le_ofReal hR
      _ = ENNReal.ofReal K * ENNReal.ofReal (d ^ (-2 * ((n : ℝ) - 1 / 2))) :=
          ENNReal.ofReal_mul hKnn
      _ ≤ ENNReal.ofReal K * ψ (e x) := by
          gcongr
          rcases (norm_nonneg (e x - vP)).eq_or_lt with h0 | hpos
          · rw [← hd] at h0
            rw [← h0, Real.zero_rpow (by
              have : (2:ℝ) ≤ n := by exact_mod_cast hn
              linarith)]
            simp
          · simp only [ψ]
            rw [ENNReal.ofReal_rpow_of_pos hpos]
  have hUm : MeasurableSet (e.source ∩ e ⁻¹' W) := hUo.measurableSet
  calc ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq la f y *
        A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu
      ≤ ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal K * ψ (e y) ∂A.mu :=
        setLIntegral_mono' hUm hpt
    _ = ENNReal.ofReal K * ∫⁻ y in e.source ∩ e ⁻¹' W, ψ (e y) ∂A.mu :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal B7 * ∫⁻ v in W, ψ v) := by
        gcongr
        exact A.lintegral_chart_le i P Metric.isOpen_ball hWt _
          (fun v hv => ENNReal.ofReal_le_ofReal (hball v (hWb hv)).2.2.2.2.2.2.le) ψ hψc
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
        exact lintegral_ball_rpow_lt_top hMVI (by omega) vP (min_le_right _ _) (by linarith)

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
