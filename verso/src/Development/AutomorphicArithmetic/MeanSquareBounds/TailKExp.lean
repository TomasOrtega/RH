import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailFinal

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Establish `hc : 0 < ε / 6` using `by positivity`. Establish `hg` using `(tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (404 * K / (ε / 6)) 1 one_pos).comp (tendsto_rpow_atTop hc)`. Establish `hlim : Filter.Tendsto (fun Y : ℝ => A * (Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6))))) Filter.atTop (nhds 0)`. Use `hg.const_mul A` as an intermediate fact. Rewrite `this` using `[mul_zero]`.

Use `this.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_gt_atTop 0] with Y hY`. Simplify using `only [Function.comp_apply, neg_mul, one_mul]`. Rewrite using `[← Real.rpow_mul hY.le, mul_div_cancel₀ _ hc.ne']`. Conclude with `hlim.eventually (ge_mem_nhds (by norm_num))`.
-/
private theorem tailK_exp (ε K A : ℝ) (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in Filter.atTop, A * (Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6)))) ≤ 1 / 3 := by
  have hc : 0 < ε / 6 := by positivity
  have hg := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (404 * K / (ε / 6)) 1 one_pos).comp
    (tendsto_rpow_atTop hc)
  have hlim : Filter.Tendsto (fun Y : ℝ => A * (Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6)))))
      Filter.atTop (nhds 0) := by
    have := hg.const_mul A
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with Y hY
    simp only [Function.comp_apply, neg_mul, one_mul]
    rw [← Real.rpow_mul hY.le, mul_div_cancel₀ _ hc.ne']
  exact hlim.eventually (ge_mem_nhds (by norm_num))

/- English proof (translation)
Establish `hev1` using `tailK_exp ε K A hε`. Establish `hev2 : ∀ᶠ Y : ℝ in Filter.atTop, 3 * A ≤ Y ^ (ε / 4)` using `(tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _`. Establish `hev3 : ∀ᶠ Y : ℝ in Filter.atTop, 3 * 802 ≤ Y ^ ε` using `(tendsto_rpow_atTop hε).eventually_ge_atTop _`. Take `⟨Y₁, hY₁⟩` from `Filter.eventually_atTop.1 (hev1.and (hev2.and hev3))`. Use `⟨max Y₁ 3, le_max_right _ _, ?_⟩` and prove the remaining obligations.

Introduce `Y x Q hY hx hQ hl1 hl2`. Establish `hY1 : Y₁ ≤ Y` using `(le_max_left _ _).trans hY`. Establish `hY3 : 3 ≤ Y` using `(le_max_right _ _).trans hY`. Take `⟨h1, h2, h3⟩` from `hY₁ Y hY1`. Establish `hY0 : 0 < Y` using `by linarith`.

Establish `hK0 : K ≠ 0` using `by positivity`. Establish `hxY : Y ≤ x`. Rewrite using `[hx]; simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) hK`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hx3 : 3 ≤ x` using `by linarith`.

Rewrite using `[Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (ε / K) hx0, Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q A (Real.log Q) (x ^ (ε / K / 4)) (Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2))) hx0 hQ]`. Establish `ha : x ^ (ε / K / 4) = Y ^ (ε / 4)`. Rewrite using `[hx, ← Real.rpow_mul hY0.le]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Establish `hlpos : 0 ≤ Real.log Q` using `le_trans (by positivity) hl1`. Establish `hu1 : Y ^ (ε / 4) ≤ Y`. Simplify using `using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) (by linarith : ε / 4 ≤ 1)`. Establish `huY : Y ^ (ε / 4) ≤ x` using `hu1.trans hxY`. Establish `hlx : Real.log Q ≤ x` using `hl2.trans huY`.

Establish `ht : Real.exp (Y ^ (ε / 6)) ≤ Q` using `(Real.le_log_iff_exp_le hQ).1 hl1`. Establish `hx404 : Y ^ (404 * K) = x ^ 404`. Rewrite using `[hx, ← Real.rpow_mul_natCast hY0.le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsecond : A * (Real.log Q * x ^ 403 / Q) ≤ 1 / 3`. Establish `hQe : 1 / Q ≤ Real.exp (-(Y ^ (ε / 6)))`. Rewrite using `[Real.exp_neg, ← one_div]`. Conclude with `one_div_le_one_div_of_le (Real.exp_pos _) ht`.

Establish `hm : Real.log Q * x ^ 403 / Q ≤ Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6)))`. Rewrite using `[hx404]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(mul_le_mul_of_nonneg_left hm hA0).trans h1`. Establish `hthird` using `Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3`.

Rewrite using `[ha]`. Establish `hu0 : 0 < Y ^ (ε / 4)` using `Real.rpow_pos_of_pos hY0 _`. Establish `hu4 : Y ^ ε = (Y ^ (ε / 4)) ^ 4`. Rewrite using `[← Real.rpow_mul_natCast hY0.le]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hfirst : A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ (Y ^ (ε / 4)) ^ 4 / 3`. Establish `hl2' : Real.log Q ^ 2 ≤ (Y ^ (ε / 4)) ^ 2` using `pow_le_pow_left₀ hlpos hl2 2`. Establish `hm : A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ A * (Y ^ (ε / 4)) ^ 3`.

Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 h2) (pow_pos hu0 3).le]`. Rewrite `h3`, the goal using `[hu4]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem tailK_num (ε K A : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K) (hA0 : 0 ≤ A) :
    ∃ Y₀ : ℝ, 3 ≤ Y₀ ∧
    ∀ Y x Q : ℝ, Y₀ ≤ Y → x = Y ^ K → 0 < Q → Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) →
      x * ((A * Real.log Q * (Real.log Q * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + ε / K / 1600) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ Y ^ ε := by
  have hev1 := tailK_exp ε K A hε
  have hev2 : ∀ᶠ Y : ℝ in Filter.atTop, 3 * A ≤ Y ^ (ε / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have hev3 : ∀ᶠ Y : ℝ in Filter.atTop, 3 * 802 ≤ Y ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop _
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1 (hev1.and (hev2.and hev3))
  refine ⟨max Y₁ 3, le_max_right _ _, ?_⟩
  intro Y x Q hY hx hQ hl1 hl2
  have hY1 : Y₁ ≤ Y := (le_max_left _ _).trans hY
  have hY3 : 3 ≤ Y := (le_max_right _ _).trans hY
  obtain ⟨h1, h2, h3⟩ := hY₁ Y hY1
  have hY0 : 0 < Y := by linarith
  have hK0 : K ≠ 0 := by positivity
  have hxY : Y ≤ x := by
    rw [hx]; simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) hK
  have hx0 : 0 < x := by linarith
  have hx3 : 3 ≤ x := by linarith
  rw [Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (ε / K) hx0,
    Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q A (Real.log Q) (x ^ (ε / K / 4))
      (Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2))) hx0 hQ]
  have ha : x ^ (ε / K / 4) = Y ^ (ε / 4) := by
    rw [hx, ← Real.rpow_mul hY0.le]
    congr 1
    field_simp
  have hlpos : 0 ≤ Real.log Q := le_trans (by positivity) hl1
  have hu1 : Y ^ (ε / 4) ≤ Y := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) (by linarith : ε / 4 ≤ 1)
  have huY : Y ^ (ε / 4) ≤ x := hu1.trans hxY
  have hlx : Real.log Q ≤ x := hl2.trans huY
  have ht : Real.exp (Y ^ (ε / 6)) ≤ Q := (Real.le_log_iff_exp_le hQ).1 hl1
  have hx404 : Y ^ (404 * K) = x ^ 404 := by
    rw [hx, ← Real.rpow_mul_natCast hY0.le]
    congr 1
    push_cast
    ring
  have hsecond : A * (Real.log Q * x ^ 403 / Q) ≤ 1 / 3 := by
    have hQe : 1 / Q ≤ Real.exp (-(Y ^ (ε / 6))) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos _) ht
    have hm : Real.log Q * x ^ 403 / Q ≤ Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6))) := by
      rw [hx404]
      calc Real.log Q * x ^ 403 / Q = Real.log Q * x ^ 403 * (1 / Q) := by ring
        _ ≤ x * x ^ 403 * Real.exp (-(Y ^ (ε / 6))) := by gcongr
        _ = x ^ 404 * Real.exp (-(Y ^ (ε / 6))) := by ring
    exact (mul_le_mul_of_nonneg_left hm hA0).trans h1
  have hthird := Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3
  rw [ha]
  have hu0 : 0 < Y ^ (ε / 4) := Real.rpow_pos_of_pos hY0 _
  have hu4 : Y ^ ε = (Y ^ (ε / 4)) ^ 4 := by
    rw [← Real.rpow_mul_natCast hY0.le]
    congr 1
    push_cast
    ring
  have hfirst : A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ (Y ^ (ε / 4)) ^ 4 / 3 := by
    have hl2' : Real.log Q ^ 2 ≤ (Y ^ (ε / 4)) ^ 2 := pow_le_pow_left₀ hlpos hl2 2
    have hm : A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ A * (Y ^ (ε / 4)) ^ 3 := by
      calc A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ A * (Y ^ (ε / 4)) ^ 2 * Y ^ (ε / 4) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl2' hA0) hu0.le
        _ = A * (Y ^ (ε / 4)) ^ 3 := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (pow_pos hu0 3).le]
  rw [hu4] at h3 ⊢
  linarith

/- English proof (translation)
Introduce `ε K hε hε1 hK`. Establish `hK0 : 0 < K` using `by linarith`. Establish `hδ0 : 0 < ε / K / 1600` using `by positivity`. Establish `hδ1 : ε / K / 1600 ≤ 1 / 800`. Establish `: ε / K ≤ 1` using `(div_le_one hK0).2 (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨A, hA0, hA⟩` from `Formalism.HermitianLattices.Ext.BoxTail.tail_contour (ε / K / 1600) hδ0 hδ1`. Take `⟨Y₀, hY₀3, hY₀⟩` from `tailK_num ε K A hε hε1 hK hA0`. Use `⟨Y₀, fun Y hY Q N _ χ hl1 hl2 hG => ?_⟩` and prove the remaining obligations. Take `⟨hχ1, hNQ, hZ⟩` from `hG`.

Establish `hY3 : 3 ≤ Y` using `le_trans hY₀3 hY`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hxY : Y ≤ Y ^ K`. Simplify using `using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) hK`. Generalize the expression as in `hxd : Y ^ K = x at hxY ⊢`.

Establish `hx0 : 0 < x` using `by linarith`. Establish `hN1 : (1:ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)`. Establish `hQ0 : 0 < Q` using `by linarith`. Establish `hc1 : 1 ≤ Y ^ (ε / 6)` using `Real.one_le_rpow (by linarith) (by positivity)`. Establish `hQ2 : 2 ≤ Q`.

Establish `e1 : Real.exp 1 ≤ Q` using `(Real.le_log_iff_exp_le hQ0).1 (hc1.trans hl1)`. Establish `e2` using `Real.add_one_le_exp (1:ℝ)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz1 : (1:ℝ) ≤ x ^ 400` using `one_le_pow₀ (by linarith)`. Establish `hη0 : (0:ℝ) < 1 / x ^ 2` using `by positivity`.

Establish `hη1 : 1 / x ^ 2 ≤ 1`. Rewrite using `[div_le_one (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hh0 : (0:ℝ) < x ^ 400 * (1 / x ^ 2)` using `by positivity`. Establish `hc` using `hA N χ Q (x ^ 400) (1 / x ^ 2) hχ1 hQ2 hNQ hZ hz1 hη0 hη1`.

Establish `hd` using `Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ (x ^ 400) (x ^ 400 * (1 / x ^ 2)) hz1 hh0`. Establish `key : ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) * tailL χ (x ^ 400) = (Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400 + x ^ 400 * (1 / x ^ 2)) - Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400) - ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) * ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) …`. Simplify using `only [tailL, Formalism.ZeroFreeDirichlet.negLD, logDerivLAtOne]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnorm` using `(norm_sub_le _ _).trans (add_le_add hd hc)`.

Rewrite `hnorm` using `[← key, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh0.le]`. Establish `hfin` using `hY₀ Y x Q hY hxd.symm hQ0 hl1 hl2`. Establish `ht : ‖tailL χ (x ^ 400)‖ ≤ (A * Real.log Q * (Real.log Q * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + ε / K / 1600) + (x ^ 400) ^ 2 / Q) + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400) / (x ^ 400 * (1 / x ^ 2))`. Rewrite using `[le_div_iff₀ hh0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]`. Conclude with `(mul_le_mul_of_nonneg_left ht hx0.le).trans hfin`.
-/
theorem tailK :
    ∀ ε K : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ →
      ‖((Y ^ K : ℝ) : ℂ) * tailL χ ((Y ^ K) ^ 400)‖ ≤ Y ^ ε := by
  intro ε K hε hε1 hK
  have hK0 : 0 < K := by linarith
  have hδ0 : 0 < ε / K / 1600 := by positivity
  have hδ1 : ε / K / 1600 ≤ 1 / 800 := by
    have : ε / K ≤ 1 := (div_le_one hK0).2 (by linarith)
    linarith
  obtain ⟨A, hA0, hA⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_contour (ε / K / 1600) hδ0 hδ1
  obtain ⟨Y₀, hY₀3, hY₀⟩ := tailK_num ε K A hε hε1 hK hA0
  refine ⟨Y₀, fun Y hY Q N _ χ hl1 hl2 hG => ?_⟩
  obtain ⟨hχ1, hNQ, hZ⟩ := hG
  have hY3 : 3 ≤ Y := le_trans hY₀3 hY
  have hY0 : 0 < Y := by linarith
  have hxY : Y ≤ Y ^ K := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) hK
  generalize hxd : Y ^ K = x at hxY ⊢
  have hx0 : 0 < x := by linarith
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  have hc1 : 1 ≤ Y ^ (ε / 6) := Real.one_le_rpow (by linarith) (by positivity)
  have hQ2 : 2 ≤ Q := by
    have e1 : Real.exp 1 ≤ Q := (Real.le_log_iff_exp_le hQ0).1 (hc1.trans hl1)
    have e2 := Real.add_one_le_exp (1:ℝ)
    linarith
  have hz1 : (1:ℝ) ≤ x ^ 400 := one_le_pow₀ (by linarith)
  have hη0 : (0:ℝ) < 1 / x ^ 2 := by positivity
  have hη1 : 1 / x ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hh0 : (0:ℝ) < x ^ 400 * (1 / x ^ 2) := by positivity
  have hc := hA N χ Q (x ^ 400) (1 / x ^ 2) hχ1 hQ2 hNQ hZ hz1 hη0 hη1
  have hd := Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ (x ^ 400) (x ^ 400 * (1 / x ^ 2)) hz1 hh0
  have key : ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) * tailL χ (x ^ 400) =
      (Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400 + x ^ 400 * (1 / x ^ 2)) - Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400) -
        ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) *
          ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n) -
      (Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400 + x ^ 400 * (1 / x ^ 2)) - Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400) -
        ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [tailL, Formalism.ZeroFreeDirichlet.negLD, logDerivLAtOne]
    ring
  have hnorm := (norm_sub_le _ _).trans (add_le_add hd hc)
  rw [← key, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh0.le] at hnorm
  have hfin := hY₀ Y x Q hY hxd.symm hQ0 hl1 hl2
  have ht : ‖tailL χ (x ^ 400)‖ ≤ (A * Real.log Q * (Real.log Q * (1 / x ^ 2) *
      (x ^ 400) ^ (1 - 1 / 400 + ε / K / 1600) + (x ^ 400) ^ 2 / Q) +
      x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) *
      Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400) / (x ^ 400 * (1 / x ^ 2)) := by
    rw [le_div_iff₀ hh0]
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  exact (mul_le_mul_of_nonneg_left ht hx0.le).trans hfin

end QH
