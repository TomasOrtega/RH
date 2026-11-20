import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailFinal
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mertensUpper

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Establish `hs0 : 0 < s` using `by linarith`. Establish `hs1 : 1 ≤ s` using `by linarith`. Establish `hx3 : 3 ≤ x`. Rewrite using `[hx]; exact hs.trans (le_self_pow₀ hs1 (by norm_num))`. Establish `hx0 : 0 < x` using `by linarith`.

Establish `hxa : x ^ ((2 / 5) / 4 : ℝ) = s`. Rewrite using `[hx, ← Real.rpow_natCast s 10, ← Real.rpow_mul hs0.le]`. Evaluate the numerical expressions. Apply `le_of_mul_le_mul_left _ hx0` to reduce the goal to its premises. Rewrite using `[Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (2 / 5) hx0, hxa, Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q K _ _ _ hx0 hQ]`.

Establish `t3` using `Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3`. Establish `t1 : (s ^ 4) ^ 2 * s ≤ x`. Rewrite using `[hx]`. Combine the equalities or inequalities in the displayed calculation. Establish `t2 : s ^ 4 * x ^ 403 / Q ≤ x`.

Rewrite using `[div_le_iff₀ hQ]`. Establish `e : s ^ 4 * x ^ 403 = x * (s ^ 4) ^ 1006`. Rewrite using `[hx, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]`. Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_left hQs hx0.le`.

Establish `u1` using `mul_le_mul_of_nonneg_left t1 hK`. Establish `u2` using `mul_le_mul_of_nonneg_left t2 hK`. Establish `u3 : (802 : ℝ) ≤ x * 802` using `by linarith`. Establish `e1 : K * (s ^ 4) ^ 2 * s = K * ((s ^ 4) ^ 2 * s)` using `mul_assoc _ _ _`. Establish `e2 : x * (2 * K + 802) = K * x + K * x + x * 802` using `by ring`.

Rewrite using `[e1, e2]`. Conclude with `add_le_add (add_le_add u1 u2) (t3.trans u3)`.
-/
private theorem kappa4_num (K : ℝ) (hK : 0 ≤ K) (s Q : ℝ) (hs : 3 ≤ s) (hQ : 0 < Q)
    (hQs : (s ^ 4) ^ 1006 ≤ Q) (x : ℝ) (hx : x = s ^ 10) :
    ((K * s ^ 4 * (s ^ 4 * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ 2 * K + 802 := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs.trans (le_self_pow₀ hs1 (by norm_num))
  have hx0 : 0 < x := by linarith
  have hxa : x ^ ((2 / 5) / 4 : ℝ) = s := by
    rw [hx, ← Real.rpow_natCast s 10, ← Real.rpow_mul hs0.le]
    norm_num
  apply le_of_mul_le_mul_left _ hx0
  rw [Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (2 / 5) hx0, hxa,
    Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q K _ _ _ hx0 hQ]
  have t3 := Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3
  have t1 : (s ^ 4) ^ 2 * s ≤ x := by
    rw [hx]
    calc (s ^ 4) ^ 2 * s = s ^ 9 := by ring
      _ ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
  have t2 : s ^ 4 * x ^ 403 / Q ≤ x := by
    rw [div_le_iff₀ hQ]
    have e : s ^ 4 * x ^ 403 = x * (s ^ 4) ^ 1006 := by
      rw [hx, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    rw [e]
    exact mul_le_mul_of_nonneg_left hQs hx0.le
  have u1 := mul_le_mul_of_nonneg_left t1 hK
  have u2 := mul_le_mul_of_nonneg_left t2 hK
  have u3 : (802 : ℝ) ≤ x * 802 := by linarith
  have e1 : K * (s ^ 4) ^ 2 * s = K * ((s ^ 4) ^ 2 * s) := mul_assoc _ _ _
  have e2 : x * (2 * K + 802) = K * x + K * x + x * 802 := by ring
  rw [e1, e2]
  exact add_le_add (add_le_add u1 u2) (t3.trans u3)

/- English proof (translation)
Take `⟨K, hK0, hK⟩` from `Formalism.HermitianLattices.Ext.BoxTail.tail_contour ((2 / 5) / 1600) (by positivity) (by norm_num)`. Establish `hev : ∀ᶠ l : ℝ in Filter.atTop, l ^ 1006 ≤ Real.exp l`. Establish `h` using `(Real.tendsto_exp_div_pow_atTop 1006).eventually_ge_atTop 1`. Use `filter_upwards [h, Filter.eventually_gt_atTop 0] with l hl hl0`. Rewrite `hl` using `[le_div_iff₀ (by positivity), one_mul]`. Then use the resulting hypothesis.

Take `⟨l₀, hl₀⟩` from `Filter.eventually_atTop.1 (hev.and (Filter.eventually_ge_atTop 81))`. Use `⟨2 * K + 802 + 2, l₀, by linarith [(hl₀ l₀ le_rfl).2], ?_⟩` and prove the remaining obligations. Introduce `Q N _ χ hQlo hgood`. Take `⟨hχ, hNQ, hbox⟩` from `hgood`. Take `⟨hexp, h81⟩` from `hl₀ _ hQlo`.

Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`. Establish `hQ0 : 0 < Q` using `by linarith`. Rewrite `hexp` using `[Real.exp_log hQ0]`. Establish `hQ2 : 2 ≤ Q`. Use `Real.log_le_self hQ0.le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨s, hs0, hs4⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 4 = Real.log Q` from `⟨Real.log Q ^ ((4 : ℕ) : ℝ)⁻¹, Real.rpow_nonneg (by linarith) _, Real.rpow_inv_natCast_pow (by linarith) (by norm_num)⟩`. Establish `hs3 : 3 ≤ s`. Apply `le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hs0` to reduce the goal to its premises. Rewrite using `[hs4]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨x, hx⟩ : ∃ x : ℝ, x = s ^ 10` from `⟨_, rfl⟩`. Establish `hnum` using `kappa4_num K hK0 s Q hs3 hQ0 (by rw [hs4]; exact hexp) x hx`. Rewrite `hnum` using `[hs4]`. Establish `hx3 : 3 ≤ x`.

Rewrite using `[hx]; exact hs3.trans (le_self_pow₀ (by linarith) (by norm_num))`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hlogz : Real.log (x ^ 400) = 1000 * Real.log (Real.log Q)`. Rewrite using `[← hs4, hx, Real.log_pow, Real.log_pow, Real.log_pow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `set z : ℝ := x ^ 400 with hz`. Use `set η : ℝ := 1 / x ^ 2 with hη`. Establish `hz1 : 1 ≤ z` using `one_le_pow₀ (by linarith)`. Establish `hη0 : 0 < η` using `by positivity`.

Establish `hη1 : η ≤ 1`. Rewrite using `[hη, div_le_one (by positivity)]; nlinarith`. Establish `hzη : 0 < z * η` using `by positivity`. Establish `hC` using `hK N χ Q z η hχ hQ2 hNQ hbox hz1 hη0 hη1`. Establish `hD` using `Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ z (z * η) hz1 hzη`.

Use `set P : ℂ := ∑ n ∈ Icc 1 ⌊z⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) with hP`. Establish `hkey : ((z * η : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.negLD χ 1 - P) = -(Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) + (Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formal …` using `by ring`. Establish `hnorm : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤ (K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + z ^ 2 / Q) + z * η * (z * η + 1) * Real.log (z + z * η) / z) / (z * η)`. Rewrite using `[le_div_iff₀ hzη]`. Establish `h1` using `congrArg norm hkey`.

Rewrite `h1` using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hzη.le]`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg]`. Conclude with `add_le_add hC hD`.

Establish `htail` using `hnorm.trans hnum`. Establish `hPle : ‖P‖ ≤ Real.log z + 2`. Establish `hM : ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤ Real.log z + 2`. Use `le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (Deduction.mertens_upper z hz1)` and prove the remaining obligations. Introduce `n hn`.

Conclude with `Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)`. Introduce `n _ _`. Conclude with `div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)`. Use `le_trans (norm_sum_le _ _) (le_trans ?_ hM)` and prove the remaining obligations. Use `Finset.sum_le_sum (fun n hn => ?_)` and prove the remaining obligations.

Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast (Finset.mem_Icc.mp hn).1`. Rewrite using `[norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]`. Establish `hχn : ‖χ (n : ZMod N)‖ ≤ 1` using `DirichletCharacter.norm_le_one χ _`. Establish `hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ)` using `ArithmeticFunction.vonMangoldt_nonneg`. Use `gcongr`.

Combine the equalities or inequalities in the displayed calculation. Establish `hLD : logDerivLAtOne χ = -(Formalism.ZeroFreeDirichlet.negLD χ 1)`. Simplify using `only [logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, neg_neg]`. Rewrite using `[hLD, norm_neg]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem kappa4_loglog : ∃ C l₀ : ℝ, 1 ≤ l₀ ∧ ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    l₀ ≤ Real.log Q → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 1000 * Real.log (Real.log Q) + C := by
  obtain ⟨K, hK0, hK⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_contour ((2 / 5) / 1600) (by positivity) (by norm_num)
  have hev : ∀ᶠ l : ℝ in Filter.atTop, l ^ 1006 ≤ Real.exp l := by
    have h := (Real.tendsto_exp_div_pow_atTop 1006).eventually_ge_atTop 1
    filter_upwards [h, Filter.eventually_gt_atTop 0] with l hl hl0
    rwa [le_div_iff₀ (by positivity), one_mul] at hl
  obtain ⟨l₀, hl₀⟩ := Filter.eventually_atTop.1 (hev.and (Filter.eventually_ge_atTop 81))
  refine ⟨2 * K + 802 + 2, l₀, by linarith [(hl₀ l₀ le_rfl).2], ?_⟩
  intro Q N _ χ hQlo hgood
  obtain ⟨hχ, hNQ, hbox⟩ := hgood
  obtain ⟨hexp, h81⟩ := hl₀ _ hQlo
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  rw [Real.exp_log hQ0] at hexp
  have hQ2 : 2 ≤ Q := by
    have := Real.log_le_self hQ0.le
    linarith
  obtain ⟨s, hs0, hs4⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 4 = Real.log Q :=
    ⟨Real.log Q ^ ((4 : ℕ) : ℝ)⁻¹, Real.rpow_nonneg (by linarith) _,
      Real.rpow_inv_natCast_pow (by linarith) (by norm_num)⟩
  have hs3 : 3 ≤ s := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hs0
    rw [hs4]; linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = s ^ 10 := ⟨_, rfl⟩
  have hnum := kappa4_num K hK0 s Q hs3 hQ0 (by rw [hs4]; exact hexp) x hx
  rw [hs4] at hnum
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs3.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hx0 : 0 < x := by linarith
  have hlogz : Real.log (x ^ 400) = 1000 * Real.log (Real.log Q) := by
    rw [← hs4, hx, Real.log_pow, Real.log_pow, Real.log_pow]; push_cast; ring
  set z : ℝ := x ^ 400 with hz
  set η : ℝ := 1 / x ^ 2 with hη
  have hz1 : 1 ≤ z := one_le_pow₀ (by linarith)
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  have hzη : 0 < z * η := by positivity
  have hC := hK N χ Q z η hχ hQ2 hNQ hbox hz1 hη0 hη1
  have hD := Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ z (z * η) hz1 hzη
  set P : ℂ := ∑ n ∈ Icc 1 ⌊z⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) with hP
  have hkey : ((z * η : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.negLD χ 1 - P) =
      -(Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) +
      (Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * P) := by ring
  have hnorm : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤
      (K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + z ^ 2 / Q)
        + z * η * (z * η + 1) * Real.log (z + z * η) / z) / (z * η) := by
    rw [le_div_iff₀ hzη]
    have h1 := congrArg norm hkey
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hzη.le] at h1
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ * (z * η) = z * η * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := mul_comm _ _
      _ = _ := h1
      _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        exact add_le_add hC hD
  have htail := hnorm.trans hnum
  have hPle : ‖P‖ ≤ Real.log z + 2 := by
    have hM : ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤ Real.log z + 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (Deduction.mertens_upper z hz1)
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
      · intro n _ _
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    refine le_trans (norm_sum_le _ _) (le_trans ?_ hM)
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχn : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    gcongr
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * ‖χ (n : ZMod N)‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 := by gcongr
      _ = ArithmeticFunction.vonMangoldt n := mul_one _
  have hLD : logDerivLAtOne χ = -(Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, neg_neg]
  rw [hLD, norm_neg]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1‖ = ‖P + (Formalism.ZeroFreeDirichlet.negLD χ 1 - P)‖ := by rw [add_sub_cancel]
    _ ≤ ‖P‖ + ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := norm_add_le _ _
    _ ≤ _ := by rw [← hlogz]; linarith

/- English proof (translation)
Introduce `ε A hε hε1 hA`. Take `⟨C, l₀, hl₀, hC⟩` from `kappa4_loglog`. Establish `e1 : ∀ᶠ Y : ℝ in Filter.atTop, l₀ ≤ Y ^ (ε / 6)` using `(tendsto_rpow_atTop (by positivity : 0 < ε / 6)).eventually_ge_atTop _`. Establish `e2 : ∀ᶠ u : ℝ in Filter.atTop, ‖Real.log u‖ ≤ (1 / 26000) * ‖u‖` using `Real.isLittleO_log_id_atTop.bound (by norm_num)`. Establish `e3 : ∀ᶠ u : ℝ in Filter.atTop, 13 * (1000 * Real.log A + C) ≤ u` using `Filter.eventually_ge_atTop _`.

Establish `e4` using `Real.tendsto_log_atTop.eventually (e2.and (e3.and (Filter.eventually_ge_atTop 1)))`. Take `⟨Y₀, hY₀⟩` from `Filter.eventually_atTop.1 (e1.and (e4.and (Filter.eventually_gt_atTop 0)))`. Use `⟨Y₀, ?_⟩` and prove the remaining obligations. Introduce `Y hY Q N _ χ hlo hhi hgood`. Take `⟨h1, ⟨h2, h3, h4⟩, hY0⟩` from `hY₀ Y hY`.

Establish `hb` using `hC Q N χ (h1.trans hlo) hgood`. Establish `hu0 : 0 < Real.log Y` using `by linarith`. Establish `hp : 0 < Y ^ (ε / 5)` using `Real.rpow_pos_of_pos hY0 _`. Establish `hl : Real.log (Real.log Q) ≤ Real.log A + ε / 5 * Real.log Y + 2 * Real.log (Real.log Y)`. Use `(Real.log_le_log (by linarith) hhi).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul hA.ne' hp.ne', Real.log_rpow hY0, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[Real.norm_of_nonneg hu0.le, Real.norm_of_nonneg (Real.log_nonneg h4)]`. Establish `h5 : ε * Real.log Y ≤ 1 / 52 * Real.log Y` using `mul_le_mul_of_nonneg_right hε1.le hu0.le`.

Establish `h6 : ε / 5 * Real.log Y = ε * Real.log Y / 5` using `by ring`. Rewrite `hl` using `[h6]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kappa4 :
    ∀ ε A : ℝ, 0 < ε → ε < 1 / 52 → 0 < A → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ A * Y ^ (ε / 5) * Real.log Y ^ 2 → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 4 * Real.log Y := by
  intro ε A hε hε1 hA
  obtain ⟨C, l₀, hl₀, hC⟩ := kappa4_loglog
  have e1 : ∀ᶠ Y : ℝ in Filter.atTop, l₀ ≤ Y ^ (ε / 6) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 6)).eventually_ge_atTop _
  have e2 : ∀ᶠ u : ℝ in Filter.atTop, ‖Real.log u‖ ≤ (1 / 26000) * ‖u‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num)
  have e3 : ∀ᶠ u : ℝ in Filter.atTop, 13 * (1000 * Real.log A + C) ≤ u := Filter.eventually_ge_atTop _
  have e4 := Real.tendsto_log_atTop.eventually (e2.and (e3.and (Filter.eventually_ge_atTop 1)))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 (e1.and (e4.and (Filter.eventually_gt_atTop 0)))
  refine ⟨Y₀, ?_⟩
  intro Y hY Q N _ χ hlo hhi hgood
  obtain ⟨h1, ⟨h2, h3, h4⟩, hY0⟩ := hY₀ Y hY
  have hb := hC Q N χ (h1.trans hlo) hgood
  have hu0 : 0 < Real.log Y := by linarith
  have hp : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hY0 _
  have hl : Real.log (Real.log Q) ≤ Real.log A + ε / 5 * Real.log Y + 2 * Real.log (Real.log Y) := by
    refine (Real.log_le_log (by linarith) hhi).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hA.ne' hp.ne', Real.log_rpow hY0,
      Real.log_pow]
    push_cast; ring
  rw [Real.norm_of_nonneg hu0.le, Real.norm_of_nonneg (Real.log_nonneg h4)] at h2
  have h5 : ε * Real.log Y ≤ 1 / 52 * Real.log Y := mul_le_mul_of_nonneg_right hε1.le hu0.le
  have h6 : ε / 5 * Real.log Y = ε * Real.log Y / 5 := by ring
  rw [h6] at hl
  linarith

end QH
