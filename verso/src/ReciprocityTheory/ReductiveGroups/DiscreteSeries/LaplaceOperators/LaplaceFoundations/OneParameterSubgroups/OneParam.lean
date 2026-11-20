import Mathlib

open MeasureTheory Complex Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

/- English proof (translation)
Establish `hδ : 0 ≤ δ` using `(norm_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)`. Establish `hofs : ∀ t : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t` using `fun t => (hasDerivAt_id t).ofReal_comp`. Use `set g : ℝ → ℂ := fun t => -(a * (t : ℂ)) - (t : ℂ) ^ 2 * b / 2 with hg_def`. Establish `hg : ∀ t : ℝ, HasDerivAt g (-(a + (t : ℂ) * b)) t`. Introduce `t`.

Establish `h3` using `((hofs t).const_mul a).neg.sub (((hofs t).pow 2).mul_const b |>.div_const 2)`. Apply the tactic sequence `exact h3.congr_deriv (by first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp)`. Use `set W : ℝ → ℂ := fun t => U t * cexp (g t) with hW`. Establish `hWd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt W ((U' t - (a + (t : ℂ) * b) * U t) * cexp (g t)) t`. Introduce `t ht`.

Use `(hder t ht).mul (hg t).cexp` as an intermediate fact. Conclude with `this.congr_deriv (by ring)`. Establish `hgre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (g t).re ≤ ‖b‖ / 2`. Introduce `t ht`. Establish `hre : (g t).re = -(t ^ 2 * b.re / 2)`.

Simplify using `only [hg_def]`. Simplify using `[Complex.mul_re, ha]`. Rewrite using `[← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hre]`.

Establish `hb1 : -b.re ≤ ‖b‖` using `(neg_le_abs b.re).trans (Complex.abs_re_le_norm b)`. Establish `ht2 : t ^ 2 ≤ 1` using `by nlinarith [ht.1, ht.2]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hb1 (sq_nonneg t), norm_nonneg b]`. Establish `hmvt` using `norm_image_sub_le_of_norm_deriv_le_segment' (f := W) (C := δ * Real.exp (‖b‖ / 2)) (fun t ht => (hWd t ht).hasDerivWithinAt) (fun t ht => by`. Establish `ht' : t ∈ Set.Icc (0 : ℝ) 1` using `Set.Ico_subset_Icc_self ht`.

Rewrite using `[norm_mul, Complex.norm_exp]`. Conclude with `mul_le_mul (hb t ht') (Real.exp_le_exp.mpr (hgre t ht')) (Real.exp_pos _).le hδ)`. Use `1 ⟨zero_le_one, le_rfl⟩`. Establish `hW0 : W 0 = 1` using `by simp [hW, hg_def, hU0]`. Establish `hg1 : g 1 + b / 2 = -a` using `by simp only [hg_def]; push_cast; ring`.

Establish `hid : U 1 * cexp (-a) - cexp (b / 2) = (W 1 - W 0) * cexp (b / 2)`. Rewrite using `[hW0, ← hg1]`. Simplify using `only [hW, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hre2 : (b / 2).re ≤ ‖b‖ / 2`.

Establish `: (b / 2).re = b.re / 2` using `by simp`. Rewrite using `[this]`. Combine the linear relations using `[Complex.re_le_norm b]`. Rewrite using `[hid, norm_mul, Complex.norm_exp]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ode_bound (U U' : ℝ → ℂ) (a b : ℂ) (ha : a.re = 0) {δ : ℝ} (hU0 : U 0 = 1)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt U (U' s) s)
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖U' s - (a + s * b) * U s‖ ≤ δ) :
    ‖U 1 * cexp (-a) - cexp (b / 2)‖ ≤ δ * Real.exp ‖b‖ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  have hofs : ∀ t : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
  set g : ℝ → ℂ := fun t => -(a * (t : ℂ)) - (t : ℂ) ^ 2 * b / 2 with hg_def
  have hg : ∀ t : ℝ, HasDerivAt g (-(a + (t : ℂ) * b)) t := by
    intro t
    have h3 := ((hofs t).const_mul a).neg.sub (((hofs t).pow 2).mul_const b |>.div_const 2)
    exact h3.congr_deriv (by first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp)
  set W : ℝ → ℂ := fun t => U t * cexp (g t) with hW
  have hWd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt W ((U' t - (a + (t : ℂ) * b) * U t) * cexp (g t)) t := by
    intro t ht
    have := (hder t ht).mul (hg t).cexp
    exact this.congr_deriv (by ring)
  have hgre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (g t).re ≤ ‖b‖ / 2 := by
    intro t ht
    have hre : (g t).re = -(t ^ 2 * b.re / 2) := by
      simp only [hg_def]
      simp [Complex.mul_re, ha]
      rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre]
    have hb1 : -b.re ≤ ‖b‖ := (neg_le_abs b.re).trans (Complex.abs_re_le_norm b)
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [mul_le_mul_of_nonneg_left hb1 (sq_nonneg t), norm_nonneg b]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := W)
    (C := δ * Real.exp (‖b‖ / 2)) (fun t ht => (hWd t ht).hasDerivWithinAt)
    (fun t ht => by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
      rw [norm_mul, Complex.norm_exp]
      exact mul_le_mul (hb t ht') (Real.exp_le_exp.mpr (hgre t ht')) (Real.exp_pos _).le hδ)
    1 ⟨zero_le_one, le_rfl⟩
  have hW0 : W 0 = 1 := by simp [hW, hg_def, hU0]
  have hg1 : g 1 + b / 2 = -a := by simp only [hg_def]; push_cast; ring
  have hid : U 1 * cexp (-a) - cexp (b / 2) = (W 1 - W 0) * cexp (b / 2) := by
    rw [hW0, ← hg1]
    simp only [hW, Complex.exp_add]
    ring
  have hre2 : (b / 2).re ≤ ‖b‖ / 2 := by
    have : (b / 2).re = b.re / 2 := by simp
    rw [this]
    linarith [Complex.re_le_norm b]
  rw [hid, norm_mul, Complex.norm_exp]
  calc ‖W 1 - W 0‖ * Real.exp (b / 2).re
      ≤ (δ * Real.exp (‖b‖ / 2) * (1 - 0)) * Real.exp (‖b‖ / 2) :=
        mul_le_mul hmvt (Real.exp_le_exp.mpr hre2) (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hδ (Real.exp_pos _).le) (by norm_num))
    _ = δ * Real.exp ‖b‖ := by rw [sub_zero, mul_one, mul_assoc, ← Real.exp_add, add_halves]

/- English proof (translation)
Establish `hsT : 1 ≤ Real.sqrt T`. Rewrite using `[show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hT`. Establish `hsT0 : 0 < Real.sqrt T` using `by linarith`. Establish `hTs : Real.sqrt T * Real.sqrt T = T` using `Real.mul_self_sqrt (by linarith)`. Establish `hw2 : ⟪w, w⟫_ℂ = 1`.

Rewrite using `[inner_self_eq_norm_sq_to_K, hw]`. Simplify using the standard rewrite rules. Establish `hin : ∀ s (v : H), ‖⟪w, u s v⟫_ℂ‖ ≤ ‖v‖` using `fun s v => (norm_inner_le_norm _ _).trans (by rw [hu, hw, one_mul])`. Establish `hin' : ∀ s (v : H), ‖⟪v, u s w⟫_ℂ‖ ≤ ‖v‖` using `fun s v => (norm_inner_le_norm _ _).trans (by rw [hu, hw, mul_one])`. Establish `hU1 : ∀ s, ‖⟪w, u s w⟫_ℂ‖ ≤ 1` using `fun s => (hin s w).trans hw.le`.

Use `ode_bound (δ := (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) / Real.sqrt T) (fun s => ⟪w, u s w⟫_ℂ) (fun s => ⟪w, u s (φ ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) • (Yl + Yp + Ym)))⟫_ℂ) ((Real.sqrt T : ℂ) * d Yl) (d ρ1) ?_ ?_ hder ?_` and prove the remaining obligations. Simplify using `[him]`. Use `show ⟪w, u 0 w⟫_ℂ = 1`. Rewrite using `[hu0, hw2]`. Introduce `s hs`.

Establish `hm` using `hmove s hs`. Take `⟨hs0, hs1⟩` from `hs`. Use `set c : ℝ := (Real.sqrt T)⁻¹ with hc_def`. Establish `hc0 : 0 < c` using `inv_pos.mpr hsT0`. Establish `hcs : c * Real.sqrt T = 1` using `inv_mul_cancel₀ hsT0.ne'`.

Establish `hτ0 : 0 ≤ s / Real.sqrt T` using `div_nonneg hs0 hsT0.le`. Establish `hτ1 : s / Real.sqrt T ≤ 1` using `(div_le_one hsT0).mpr (hs1.trans hsT)`. Establish `hτc : s / Real.sqrt T = s * c` using `by rw [hc_def, div_eq_mul_inv]`. Use `set τ := s / Real.sqrt T with hτ`. Establish `he₂` using `hρ τ ⟨hτ0, hτ1⟩`.

Use `set e₂ := ρ τ - Ym - (τ : ℂ) • ρ1 with he₂_def`. Use `set X := ρ τ - Ym with hX`. Establish `hXe : X = (τ : ℂ) • ρ1 + e₂` using `by rw [he₂_def]; abel`. Establish `hstρ : st (ρ τ) = st Ym + st X` using `by rw [← hstadd, hX]; congr 1; abel`. Establish `hdX : d X = (τ : ℂ) * d ρ1 + d e₂` using `by rw [hXe, map_add, map_smul, smul_eq_mul]`.

Establish `e1 : φ Yl = ((T : ℂ) * d Yl) • w + (φ Yl - ((T : ℂ) * d Yl) • w)` using `by abel`. Establish `e3 : φ (st X) = ((T : ℂ) * d (st X)) • w + (φ (st X) - ((T : ℂ) * d (st X)) • w)` using `by abel`. Establish `he3` using `hall (st X)`. Use `set E1 := φ Yl - ((T : ℂ) * d Yl) • w with hE1`. Use `set E3 := φ (st X) - ((T : ℂ) * d (st X)) • w with hE3`.

Establish `h1r : c * T = Real.sqrt T`. Combine the equalities or inequalities in the displayed calculation. Establish `h2r : c * T * τ = s`. Rewrite using `[h1r, hτc]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1 : (c : ℂ) * (T : ℂ) = (Real.sqrt T : ℂ)` using `by exact_mod_cast h1r`. Establish `h2 : (c : ℂ) * (T : ℂ) * (τ : ℂ) = (s : ℂ)` using `by exact_mod_cast h2r`. Establish `hmain : ⟪w, u s (φ ((c : ℂ) • (Yl + Yp + Ym)))⟫_ℂ - ((Real.sqrt T : ℂ) * d Yl + (s : ℂ) * d ρ1) * ⟪w, u s w⟫_ℂ = (c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ + (c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ + (c : ℂ) * ⟪E3, u s w⟫_ℂ`. Simplify using `only [map_smul, map_add, inner_smul_right, inner_add_right]`. Rewrite using `[hm, hstρ, map_add, inner_add_left, e1, e3]`.

Simplify using `only [map_add, map_smul, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left, hdst, map_mul, Complex.conj_ofReal, Complex.conj_conj, RCLike.conj_conj, hdX]`. Take the linear combination `(d Yl * ⟪w, u s w⟫_ℂ) * h1 + (d ρ1 * ⟪w, u s w⟫_ℂ) * h2`. Rewrite using `[hmain]`. Establish `hT0 : (0 : ℝ) ≤ T` using `by linarith`. Establish `hcn : ‖(c : ℂ)‖ = c` using `Complex.norm_of_nonneg hc0.le`.

Establish `b1 : ‖(c : ℂ) * ⟪w, u s E1⟫_ℂ‖ ≤ c * C`. Rewrite using `[norm_mul, hcn]`. Conclude with `mul_le_mul_of_nonneg_left ((hin s E1).trans hc) hc0.le`. Establish `b2 : ‖(c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ‖ ≤ c * C`. Rewrite using `[norm_mul, hcn]`.

Conclude with `mul_le_mul_of_nonneg_left ((hin s _).trans ha) hc0.le`. Establish `b3 : ‖(c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ‖ ≤ c * C`. Rewrite using `[norm_mul, hcn]`. Conclude with `mul_le_mul_of_nonneg_left ((hin' s _).trans ha') hc0.le`. Establish `hτs : τ = s * c` using `hτc`.

Establish `hTτ : T * τ ^ 2 ≤ 1`. Establish `e : T * τ ^ 2 = s ^ 2`. Rewrite using `[hτs, ← hTs]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hde2 : ‖d e₂‖ ≤ Cd * (K * τ ^ 2)` using `(hd e₂).trans (mul_le_mul_of_nonneg_left he₂ hCd)`. Establish `b4 : ‖(c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ‖ ≤ c * (Cd * K)`. Rewrite using `[norm_mul, norm_mul, norm_mul, hcn, Complex.norm_of_nonneg hT0]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hXb : ‖X‖ ≤ τ * ‖ρ1‖ + K * τ ^ 2`. Rewrite using `[hXe]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul, Complex.norm_of_nonneg hτ0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc1 : c ≤ 1` using `by rw [hc_def]; exact inv_le_one_of_one_le₀ hsT`. Establish `hτc' : τ ≤ c` using `by rw [hτs]; nlinarith`. Establish `hτ2 : τ ^ 2 ≤ c` using `by nlinarith`. Establish `b5 : ‖(c : ℂ) * ⟪E3, u s w⟫_ℂ‖ ≤ C * Cs * (c * ‖ρ1‖ + K * c)`. Rewrite using `[norm_mul, hcn]`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hc0.le` to reduce the goal to its premises. Use `(hin' s E3).trans (he3.trans ?_)` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_left _ (mul_nonneg hC hsT0.le)` to reduce the goal to its premises. Conclude with `(hst X).trans (mul_le_mul_of_nonneg_left hXb hCs)`.

Use `_ = C * Cs * (τ * ‖ρ1‖ + K * τ ^ 2) * (c * Real.sqrt T) := by ring`. Use `_ = C * Cs * (τ * ‖ρ1‖ + K * τ ^ 2) := by rw [hcs, mul_one]`. Use `_ ≤ C * Cs * (c * ‖ρ1‖ + K * c) := by`. Establish `q1` using `mul_le_mul_of_nonneg_right hτc' (norm_nonneg ρ1)`. Establish `q2` using `mul_le_mul_of_nonneg_left hτ2 hK`.

Establish `q3 : τ * ‖ρ1‖ + K * τ ^ 2 ≤ c * ‖ρ1‖ + K * c` using `add_le_add q1 q2`. Conclude with `mul_le_mul_of_nonneg_left q3 (mul_nonneg hC hCs)`. Establish `n4` using `norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ + (c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ) ((c : ℂ) * ⟪E3, u s w⟫_ℂ)`. Establish `n3` using `norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ) ((c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ)`. Establish `n2` using `norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ) ((c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ)`.

Establish `n1` using `norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ) ((c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ)`. Establish `hR : c * C + c * C + c * C + c * (Cd * K) + C * Cs * (c * ‖ρ1‖ + K * c) = (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) * c` using `by ring`. Rewrite using `[div_eq_mul_inv, ← hc_def]`. Combine the linear relations using `[n1, n2, n3, n4, b1, b2, b3, b4, b5, hR]`.
-/
theorem one_param {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (w : H) (hw : ‖w‖ = 1) (φ : V →ₗ[ℂ] H) (d : V →ₗ[ℂ] ℂ) (st : V → V)
    {C Cd Cs K T : ℝ} (hC : 0 ≤ C) (hCd : 0 ≤ Cd) (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hT : 1 ≤ T)
    (hd : ∀ X, ‖d X‖ ≤ Cd * ‖X‖) (hst : ∀ X, ‖st X‖ ≤ Cs * ‖X‖)
    (hstadd : ∀ X X', st (X + X') = st X + st X') (hdst : ∀ X, d (st X) = starRingEnd ℂ (d X))
    (Yl Yp Ym ρ1 : V) (ρ : ℝ → V) (him : (d Yl).re = 0)
    (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖ρ τ - Ym - (τ : ℂ) • ρ1‖ ≤ K * τ ^ 2)
    (ha : ‖φ Yp‖ ≤ C) (ha' : ‖φ (st Ym)‖ ≤ C) (hc : ‖φ Yl - ((T : ℂ) * d Yl) • w‖ ≤ C)
    (hall : ∀ X, ‖φ X - ((T : ℂ) * d X) • w‖ ≤ C * Real.sqrt T * ‖X‖)
    (u : ℝ → H →L[ℂ] H) (hu : ∀ s v, ‖u s v‖ = ‖v‖) (hu0 : u 0 w = w)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s => ⟪w, u s w⟫_ℂ)
      ⟪w, u s (φ ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) • (Yl + Yp + Ym)))⟫_ℂ s)
    (hmove : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ⟪w, u s (φ Ym)⟫_ℂ = ⟪φ (st (ρ (s / Real.sqrt T))), u s w⟫_ℂ) :
    ‖⟪w, u 1 w⟫_ℂ * cexp (-((Real.sqrt T : ℂ) * d Yl)) - cexp (d ρ1 / 2)‖ ≤
      (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) / Real.sqrt T * Real.exp ‖d ρ1‖ := by
  have hsT : 1 ≤ Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hT
  have hsT0 : 0 < Real.sqrt T := by linarith
  have hTs : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (by linarith)
  have hw2 : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hin : ∀ s (v : H), ‖⟪w, u s v⟫_ℂ‖ ≤ ‖v‖ := fun s v =>
    (norm_inner_le_norm _ _).trans (by rw [hu, hw, one_mul])
  have hin' : ∀ s (v : H), ‖⟪v, u s w⟫_ℂ‖ ≤ ‖v‖ := fun s v =>
    (norm_inner_le_norm _ _).trans (by rw [hu, hw, mul_one])
  have hU1 : ∀ s, ‖⟪w, u s w⟫_ℂ‖ ≤ 1 := fun s => (hin s w).trans hw.le
  refine ode_bound (δ := (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) / Real.sqrt T)
    (fun s => ⟪w, u s w⟫_ℂ)
    (fun s => ⟪w, u s (φ ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) • (Yl + Yp + Ym)))⟫_ℂ)
    ((Real.sqrt T : ℂ) * d Yl) (d ρ1) ?_ ?_ hder ?_
  · simp [him]
  · show ⟪w, u 0 w⟫_ℂ = 1
    rw [hu0, hw2]
  intro s hs
  have hm := hmove s hs
  obtain ⟨hs0, hs1⟩ := hs
  set c : ℝ := (Real.sqrt T)⁻¹ with hc_def
  have hc0 : 0 < c := inv_pos.mpr hsT0
  have hcs : c * Real.sqrt T = 1 := inv_mul_cancel₀ hsT0.ne'
  have hτ0 : 0 ≤ s / Real.sqrt T := div_nonneg hs0 hsT0.le
  have hτ1 : s / Real.sqrt T ≤ 1 := (div_le_one hsT0).mpr (hs1.trans hsT)
  have hτc : s / Real.sqrt T = s * c := by rw [hc_def, div_eq_mul_inv]
  set τ := s / Real.sqrt T with hτ
  have he₂ := hρ τ ⟨hτ0, hτ1⟩
  set e₂ := ρ τ - Ym - (τ : ℂ) • ρ1 with he₂_def
  set X := ρ τ - Ym with hX
  have hXe : X = (τ : ℂ) • ρ1 + e₂ := by rw [he₂_def]; abel
  have hstρ : st (ρ τ) = st Ym + st X := by rw [← hstadd, hX]; congr 1; abel
  have hdX : d X = (τ : ℂ) * d ρ1 + d e₂ := by rw [hXe, map_add, map_smul, smul_eq_mul]
  have e1 : φ Yl = ((T : ℂ) * d Yl) • w + (φ Yl - ((T : ℂ) * d Yl) • w) := by abel
  have e3 : φ (st X) = ((T : ℂ) * d (st X)) • w + (φ (st X) - ((T : ℂ) * d (st X)) • w) := by abel
  have he3 := hall (st X)
  set E1 := φ Yl - ((T : ℂ) * d Yl) • w with hE1
  set E3 := φ (st X) - ((T : ℂ) * d (st X)) • w with hE3
  have h1r : c * T = Real.sqrt T := by
    calc c * T = c * (Real.sqrt T * Real.sqrt T) := by rw [hTs]
      _ = (c * Real.sqrt T) * Real.sqrt T := by ring
      _ = Real.sqrt T := by rw [hcs, one_mul]
  have h2r : c * T * τ = s := by
    rw [h1r, hτc]
    calc Real.sqrt T * (s * c) = s * (c * Real.sqrt T) := by ring
      _ = s := by rw [hcs, mul_one]
  have h1 : (c : ℂ) * (T : ℂ) = (Real.sqrt T : ℂ) := by exact_mod_cast h1r
  have h2 : (c : ℂ) * (T : ℂ) * (τ : ℂ) = (s : ℂ) := by exact_mod_cast h2r
  have hmain : ⟪w, u s (φ ((c : ℂ) • (Yl + Yp + Ym)))⟫_ℂ
      - ((Real.sqrt T : ℂ) * d Yl + (s : ℂ) * d ρ1) * ⟪w, u s w⟫_ℂ
      = (c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ
        + (c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ + (c : ℂ) * ⟪E3, u s w⟫_ℂ := by
    simp only [map_smul, map_add, inner_smul_right, inner_add_right]
    rw [hm, hstρ, map_add, inner_add_left, e1, e3]
    simp only [map_add, map_smul, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left,
      hdst, map_mul, Complex.conj_ofReal, Complex.conj_conj, RCLike.conj_conj, hdX]
    linear_combination (d Yl * ⟪w, u s w⟫_ℂ) * h1 + (d ρ1 * ⟪w, u s w⟫_ℂ) * h2
  rw [hmain]
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hcn : ‖(c : ℂ)‖ = c := Complex.norm_of_nonneg hc0.le
  have b1 : ‖(c : ℂ) * ⟪w, u s E1⟫_ℂ‖ ≤ c * C := by
    rw [norm_mul, hcn]; exact mul_le_mul_of_nonneg_left ((hin s E1).trans hc) hc0.le
  have b2 : ‖(c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ‖ ≤ c * C := by
    rw [norm_mul, hcn]; exact mul_le_mul_of_nonneg_left ((hin s _).trans ha) hc0.le
  have b3 : ‖(c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ‖ ≤ c * C := by
    rw [norm_mul, hcn]; exact mul_le_mul_of_nonneg_left ((hin' s _).trans ha') hc0.le
  have hτs : τ = s * c := hτc
  have hTτ : T * τ ^ 2 ≤ 1 := by
    have e : T * τ ^ 2 = s ^ 2 := by
      rw [hτs, ← hTs]
      calc Real.sqrt T * Real.sqrt T * (s * c) ^ 2 = s ^ 2 * (c * Real.sqrt T) ^ 2 := by ring
        _ = s ^ 2 := by rw [hcs, one_pow, mul_one]
    rw [e]; nlinarith
  have hde2 : ‖d e₂‖ ≤ Cd * (K * τ ^ 2) := (hd e₂).trans (mul_le_mul_of_nonneg_left he₂ hCd)
  have b4 : ‖(c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ‖ ≤ c * (Cd * K) := by
    rw [norm_mul, norm_mul, norm_mul, hcn, Complex.norm_of_nonneg hT0]
    calc c * T * ‖d e₂‖ * ‖⟪w, u s w⟫_ℂ‖ ≤ c * T * (Cd * (K * τ ^ 2)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hde2 (mul_nonneg hc0.le hT0)) (hU1 s)
            (norm_nonneg _) (mul_nonneg (mul_nonneg hc0.le hT0) (mul_nonneg hCd (mul_nonneg hK (sq_nonneg τ))))
      _ = c * (Cd * K) * (T * τ ^ 2) := by ring
      _ ≤ c * (Cd * K) * 1 := mul_le_mul_of_nonneg_left hTτ (mul_nonneg hc0.le (mul_nonneg hCd hK))
      _ = c * (Cd * K) := mul_one _
  have hXb : ‖X‖ ≤ τ * ‖ρ1‖ + K * τ ^ 2 := by
    rw [hXe]
    calc ‖(τ : ℂ) • ρ1 + e₂‖ ≤ ‖(τ : ℂ) • ρ1‖ + ‖e₂‖ := norm_add_le _ _
      _ ≤ τ * ‖ρ1‖ + K * τ ^ 2 := by
        rw [norm_smul, Complex.norm_of_nonneg hτ0]; linarith
  have hc1 : c ≤ 1 := by rw [hc_def]; exact inv_le_one_of_one_le₀ hsT
  have hτc' : τ ≤ c := by rw [hτs]; nlinarith
  have hτ2 : τ ^ 2 ≤ c := by nlinarith
  have b5 : ‖(c : ℂ) * ⟪E3, u s w⟫_ℂ‖ ≤ C * Cs * (c * ‖ρ1‖ + K * c) := by
    rw [norm_mul, hcn]
    calc c * ‖⟪E3, u s w⟫_ℂ‖ ≤ c * (C * Real.sqrt T * (Cs * (τ * ‖ρ1‖ + K * τ ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ hc0.le
          refine (hin' s E3).trans (he3.trans ?_)
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hsT0.le)
          exact (hst X).trans (mul_le_mul_of_nonneg_left hXb hCs)
      _ = C * Cs * (τ * ‖ρ1‖ + K * τ ^ 2) * (c * Real.sqrt T) := by ring
      _ = C * Cs * (τ * ‖ρ1‖ + K * τ ^ 2) := by rw [hcs, mul_one]
      _ ≤ C * Cs * (c * ‖ρ1‖ + K * c) := by
          have q1 := mul_le_mul_of_nonneg_right hτc' (norm_nonneg ρ1)
          have q2 := mul_le_mul_of_nonneg_left hτ2 hK
          have q3 : τ * ‖ρ1‖ + K * τ ^ 2 ≤ c * ‖ρ1‖ + K * c := add_le_add q1 q2
          exact mul_le_mul_of_nonneg_left q3 (mul_nonneg hC hCs)
  have n4 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ
    + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ + (c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ) ((c : ℂ) * ⟪E3, u s w⟫_ℂ)
  have n3 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ
    + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ) ((c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ)
  have n2 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ)
    ((c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ)
  have n1 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ) ((c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ)
  have hR : c * C + c * C + c * C + c * (Cd * K) + C * Cs * (c * ‖ρ1‖ + K * c)
      = (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) * c := by ring
  rw [div_eq_mul_inv, ← hc_def]
  linarith [n1, n2, n3, n4, b1, b2, b3, b4, b5, hR]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
