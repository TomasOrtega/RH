import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LdrInvSubOneLe

open Complex Metric

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Use `set T := |t| with hTdef`. Use `set L := Real.log (T + 2) with hLdef`. Establish `hLpos : 0 < L` using `by linarith`. Establish `hT0 : 0 ≤ T` using `abs_nonneg t`. Establish `hLX : L ≤ T + 1`.

Use `Real.log_le_sub_one_of_pos (show 0 < T + 2 by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT3 : 3 ≤ T` using `by linarith`. Use `set u := 1 / L with hudef`. Establish `hu : 0 < u` using `by positivity`.

Establish `hu24 : u ≤ 1 / 24` using `one_div_le_one_div_of_le (by norm_num) hL`. Establish `hLu : L * u = 1` using `by rw [hudef]; field_simp`. Use `set σ₀ := 1 + u with hσ₀def`. Establish `hσ₀1 : 1 < σ₀` using `by linarith`. Establish `hσ₀2 : σ₀ ≤ 2` using `by linarith`.

Establish `hσK : 2 / (σ₀ - 1) ≤ 20000 * (T + 2)`. Establish `e : 2 / (σ₀ - 1) = 2 * L`. Rewrite using `[show σ₀ - 1 = u by ring, hudef, div_div_eq_mul_div, div_one]`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set z₀ : ℂ := (σ₀ : ℂ) + t * I with hz₀`. Establish `hz0re : z₀.re = σ₀` using `by simp [z₀]`. Establish `hz0 : riemannZeta z₀ ≠ 0` using `riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; exact hσ₀1)`. Establish `hM` using `zfo_M_bound hG hI hσ₀1 hσ₀2 hσK hT3 hT3 (by linarith)`. Establish `hM1 : 1 ≤ (T + 2) ^ 10` using `one_le_pow₀ (by linarith)`.

Take `⟨Z, m, hZ, hm, hsum, hder⟩` from `hLL riemannZeta z₀ (1 / 2) ((T + 2) ^ 10) (by norm_num) hM1 (zfo_diff_ball hT3) hz0 hM`. Establish `hlogM : Real.log ((T + 2) ^ 10) = 10 * L`. Rewrite using `[Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hsum`, `hder` using `[hlogM]`. Use `set s : ℂ := (σ : ℂ) + t * I with hsdef`. Establish `hsre : s.re = σ` using `by simp [s]`. Establish `hsim : s.im = t` using `by simp [s]`. Establish `hsz : s - z₀ = ((σ - σ₀ : ℝ) : ℂ)`.

Simplify using `only [s, z₀, Complex.ofReal_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs_mem : s ∈ closedBall z₀ (1 / 2 / 6)`. Rewrite using `[mem_closedBall, dist_eq_norm, hsz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ht0 : t ≠ 0`. Introduce `h`. Rewrite `hTdef` using `[h, abs_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs1 : s ≠ 1`.

Introduce `h`. Use `congrArg Complex.im h` as an intermediate fact. Rewrite `this` using `[hsim, Complex.one_im]`. Conclude with `ht0 this`. Establish `hc4 : (c₀ / 4) / L ≤ c₀ / L` using `div_le_div_of_nonneg_right (by linarith) hLpos.le`.

Establish `hs_ne : riemannZeta s ≠ 0`. Apply `hZ0 s hs1` to reduce the goal to its premises. Rewrite using `[hsre, hsim]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD` using `hder s hs_mem hs_ne`.

Use `set δ := (c₀ / 4) / L with hδdef`. Establish `hδ : 0 < δ` using `by positivity`. Establish `hterm : ∀ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ ≤ (m ρ : ℝ) / δ`. Introduce `ρ hρ`. Take `⟨hρb, hρ0⟩` from `(hZ ρ).1 hρ`.

Rewrite `hρb` using `[mem_closedBall, dist_eq_norm]`. Establish `him : |ρ.im - t| ≤ 1 / 6`. Establish `h1 : (ρ - z₀).im = ρ.im - t` using `by simp [z₀]`. Rewrite using `[← h1]; exact (Complex.abs_im_le_norm _).trans (by linarith)`. Establish `hρim : |ρ.im| ≤ T + 1 / 6`.

Use `abs_sub_abs_le_abs_sub ρ.im t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hρim' : T - 1 / 6 ≤ |ρ.im|`. Use `abs_sub_abs_le_abs_sub t ρ.im` as an intermediate fact. Rewrite `this` using `[abs_sub_comm]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hρ1 : ρ ≠ 1`. Introduce `h`. Rewrite `hρim'` using `[h, Complex.one_im, abs_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hre : ρ.re < 1 - c₀ / Real.log (|ρ.im| + 2)`. Assume the negation of the conclusion as `hc`. Conclude with `hZ0 ρ hρ1 (not_lt.mp hc) hρ0`. Establish `hlogρ : Real.log (|ρ.im| + 2) ≤ 2 * L`. Establish `e : 2 * L = Real.log ((T + 2) ^ 2)` using `by rw [Real.log_pow]; push_cast; ring`.

Rewrite using `[e]`. Conclude with `Real.log_le_log (by positivity) (by nlinarith)`. Establish `hlogρpos : 0 < Real.log (|ρ.im| + 2)` using `Real.log_pos (by linarith [abs_nonneg ρ.im])`. Establish `h2 : c₀ / (2 * L) ≤ c₀ / Real.log (|ρ.im| + 2)` using `div_le_div_of_nonneg_left hc₀.le hlogρpos hlogρ`. Establish `h3 : c₀ / (2 * L) = 2 * δ` using `by rw [hδdef]; field_simp; ring`.

Establish `hsρ : δ < (s - ρ).re` using `by rw [Complex.sub_re, hsre]; linarith`. Establish `hn : δ < ‖s - ρ‖` using `lt_of_lt_of_le hsρ (Complex.re_le_norm _)`. Rewrite using `[norm_div, Complex.norm_natCast]`. Conclude with `div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ hn.le`. Establish `hSm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (60 / c₀) * L ^ 2`.

Establish `h1 : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / δ` using `(norm_sum_le _ _).trans (Finset.sum_le_sum hterm)`. Establish `h2 : ∑ ρ ∈ Z, (m ρ : ℝ) / δ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ`. Rewrite using `[← Finset.sum_div]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hlog2 : (2 : ℝ) / 3 < Real.log 2`. Use `Real.log_two_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl2pos : 0 < Real.log 2` using `by linarith`. Establish `h3 : 10 * L / Real.log 2 ≤ 15 * L`.

Rewrite using `[div_le_iff₀ hl2pos]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ ≤ 15 * L / δ` using `div_le_div_of_nonneg_right (hsum.trans h3) hδ.le`. Establish `h5 : 15 * L / δ = (60 / c₀) * L ^ 2` using `by rw [hδdef]; field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hinv : ‖1 / (s - 1)‖ ≤ 1` using `ldr_inv_sub_one_le (by rw [hsim]; linarith)`. Establish `hsplit : deriv riemannZeta s / riemannZeta s + 1 / (s - 1) = (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) + 1 / (s - 1)` using `by ring`. Establish `hD' : (72 : ℝ) * (10 * L) / (1 / 2) = 1440 * L` using `by ring`. Rewrite `hD` using `[hD']`. Establish `htot : ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ 1440 * L + (60 / c₀) * L ^ 2 + 1`.

Rewrite using `[hsplit]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Use `norm_add_le (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL1 : 1 ≤ L` using `by linarith`.

Establish `hLL2 : L ≤ L ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma ldr_mid {c₀ : ℝ}
    (hZ0 : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (hc₀ : 0 < c₀) (hG : ZetaGrowth) (hI : ZetaInvBound) (hLL : LandauLocal) {σ t : ℝ}
    (hL : 24 ≤ Real.log (|t| + 2))
    (hσlo : 1 - (c₀ / 4) / Real.log (|t| + 2) ≤ σ) (hσlo' : 1 - 1 / Real.log (|t| + 2) ≤ σ)
    (hσhi : σ ≤ 1 + 1 / Real.log (|t| + 2)) :
    ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)
        + 1 / (((σ : ℂ) + t * I) - 1)‖
      ≤ (1441 + 60 / c₀) * Real.log (|t| + 2) ^ 2 := by
  set T := |t| with hTdef
  set L := Real.log (T + 2) with hLdef
  have hLpos : 0 < L := by linarith
  have hT0 : 0 ≤ T := abs_nonneg t
  have hLX : L ≤ T + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < T + 2 by linarith)
    linarith
  have hT3 : 3 ≤ T := by linarith
  set u := 1 / L with hudef
  have hu : 0 < u := by positivity
  have hu24 : u ≤ 1 / 24 := one_div_le_one_div_of_le (by norm_num) hL
  have hLu : L * u = 1 := by rw [hudef]; field_simp
  set σ₀ := 1 + u with hσ₀def
  have hσ₀1 : 1 < σ₀ := by linarith
  have hσ₀2 : σ₀ ≤ 2 := by linarith
  have hσK : 2 / (σ₀ - 1) ≤ 20000 * (T + 2) := by
    have e : 2 / (σ₀ - 1) = 2 * L := by
      rw [show σ₀ - 1 = u by ring, hudef, div_div_eq_mul_div, div_one]
    rw [e]; linarith
  set z₀ : ℂ := (σ₀ : ℂ) + t * I with hz₀
  have hz0re : z₀.re = σ₀ := by simp [z₀]
  have hz0 : riemannZeta z₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; exact hσ₀1)
  have hM := zfo_M_bound hG hI hσ₀1 hσ₀2 hσK hT3 hT3 (by linarith)
  have hM1 : 1 ≤ (T + 2) ^ 10 := one_le_pow₀ (by linarith)
  obtain ⟨Z, m, hZ, hm, hsum, hder⟩ :=
    hLL riemannZeta z₀ (1 / 2) ((T + 2) ^ 10) (by norm_num) hM1 (zfo_diff_ball hT3) hz0 hM
  have hlogM : Real.log ((T + 2) ^ 10) = 10 * L := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlogM] at hsum hder
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hsz : s - z₀ = ((σ - σ₀ : ℝ) : ℂ) := by
    simp only [s, z₀, Complex.ofReal_sub]; ring
  have hs_mem : s ∈ closedBall z₀ (1 / 2 / 6) := by
    rw [mem_closedBall, dist_eq_norm, hsz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at hTdef; linarith
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.one_im] at this; exact ht0 this
  have hc4 : (c₀ / 4) / L ≤ c₀ / L := div_le_div_of_nonneg_right (by linarith) hLpos.le
  have hs_ne : riemannZeta s ≠ 0 := by
    apply hZ0 s hs1
    rw [hsre, hsim]; linarith
  have hD := hder s hs_mem hs_ne

  set δ := (c₀ / 4) / L with hδdef
  have hδ : 0 < δ := by positivity
  have hterm : ∀ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ ≤ (m ρ : ℝ) / δ := by
    intro ρ hρ
    obtain ⟨hρb, hρ0⟩ := (hZ ρ).1 hρ
    rw [mem_closedBall, dist_eq_norm] at hρb
    have him : |ρ.im - t| ≤ 1 / 6 := by
      have h1 : (ρ - z₀).im = ρ.im - t := by simp [z₀]
      rw [← h1]; exact (Complex.abs_im_le_norm _).trans (by linarith)
    have hρim : |ρ.im| ≤ T + 1 / 6 := by
      have := abs_sub_abs_le_abs_sub ρ.im t; linarith
    have hρim' : T - 1 / 6 ≤ |ρ.im| := by
      have := abs_sub_abs_le_abs_sub t ρ.im; rw [abs_sub_comm] at this; linarith
    have hρ1 : ρ ≠ 1 := by
      intro h; rw [h, Complex.one_im, abs_zero] at hρim'; linarith
    have hre : ρ.re < 1 - c₀ / Real.log (|ρ.im| + 2) := by
      by_contra hc; exact hZ0 ρ hρ1 (not_lt.mp hc) hρ0
    have hlogρ : Real.log (|ρ.im| + 2) ≤ 2 * L := by
      have e : 2 * L = Real.log ((T + 2) ^ 2) := by rw [Real.log_pow]; push_cast; ring
      rw [e]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hlogρpos : 0 < Real.log (|ρ.im| + 2) :=
      Real.log_pos (by linarith [abs_nonneg ρ.im])
    have h2 : c₀ / (2 * L) ≤ c₀ / Real.log (|ρ.im| + 2) :=
      div_le_div_of_nonneg_left hc₀.le hlogρpos hlogρ
    have h3 : c₀ / (2 * L) = 2 * δ := by rw [hδdef]; field_simp; ring
    have hsρ : δ < (s - ρ).re := by rw [Complex.sub_re, hsre]; linarith
    have hn : δ < ‖s - ρ‖ := lt_of_lt_of_le hsρ (Complex.re_le_norm _)
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ hn.le
  have hSm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (60 / c₀) * L ^ 2 := by
    have h1 : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / δ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    have h2 : ∑ ρ ∈ Z, (m ρ : ℝ) / δ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ := by
      rw [← Finset.sum_div]; push_cast; rfl
    have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hl2pos : 0 < Real.log 2 := by linarith
    have h3 : 10 * L / Real.log 2 ≤ 15 * L := by
      rw [div_le_iff₀ hl2pos]; nlinarith
    have h4 : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ ≤ 15 * L / δ :=
      div_le_div_of_nonneg_right (hsum.trans h3) hδ.le
    have h5 : 15 * L / δ = (60 / c₀) * L ^ 2 := by rw [hδdef]; field_simp; ring
    linarith
  have hinv : ‖1 / (s - 1)‖ ≤ 1 := ldr_inv_sub_one_le (by rw [hsim]; linarith)
  have hsplit : deriv riemannZeta s / riemannZeta s + 1 / (s - 1) =
      (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
        + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) + 1 / (s - 1) := by ring
  have hD' : (72 : ℝ) * (10 * L) / (1 / 2) = 1440 * L := by ring
  rw [hD'] at hD
  have htot : ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ 1440 * L + (60 / c₀) * L ^ 2 + 1 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
      (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hLL2 : L ≤ L ^ 2 := by nlinarith
  nlinarith

end Formalism.ZF
