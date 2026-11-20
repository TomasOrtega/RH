import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDefs

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

/- English proof (translation)
Rewrite using `[Complex.norm_natCast_cpow_of_pos (by omega)]`. Apply `Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)` to reduce the goal to its premises. Simplify using `only [Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_cpow_neg_le_one' {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
  simp only [Complex.neg_re]
  linarith

/- English proof (translation)
Establish `harg : (n : ℂ).arg ≠ Real.pi`. Rewrite using `[Complex.natCast_arg]`. Conclude with `Real.pi_ne_zero.symm`. Rewrite using `[show -(starRingEnd ℂ) z = (starRingEnd ℂ) (-z) from (map_neg _ _).symm, Complex.cpow_conj _ _ harg, Complex.conj_natCast]`.
-/
lemma conj_natCast_cpow_neg (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  rw [show -(starRingEnd ℂ) z = (starRingEnd ℂ) (-z) from (map_neg _ _).symm,
    Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/- English proof (translation)
Introduce `hDual hPair C hC hL Q hQ Y N U J hU hJ hsmall T ρ hT`. Establish `hU0 : (0 : ℝ) < U` using `Nat.cast_pos.mpr (by omega)`. Establish `hJ0 : (0 : ℝ) < J` using `Nat.cast_pos.mpr (by omega)`. Establish `hs0 : s0 = 1 - 1 / 400` using `rfl`. Establish `hQ0 : (0 : ℝ) < Q` using `by linarith`.

Use `set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(s0 : ℂ)) with hb`. Use `set v : PC → ℕ → ℂ := fun p n => cv p n * (n : ℂ) ^ (-(ρ p - (s0 : ℂ))) with hv`. Use `set Δ : ℝ := (U : ℝ) + T.card * (8 * Q ^ 3) with hΔ`. Establish `hΔ0 : 0 ≤ Δ` using `by positivity`. Establish `hcv : ∀ p n, ‖cv p n‖ ≤ 1` using `fun p n => DirichletCharacter.norm_le_one _ _`.

Establish `hmemn : ∀ n ∈ Ioc U (2 * U), 0 < n` using `fun n hn => by`. Use `(Finset.mem_Ioc.mp hn).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hrow : ∀ i ∈ T, ∑ j ∈ T, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ`. Introduce `i hi`.

Rewrite using `[← Finset.add_sum_erase T _ hi]`. Establish `hdiag : ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ ≤ U`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `hone : ∀ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ 1`. Introduce `n hn`.

Rewrite using `[norm_mul, RCLike.norm_conj]`. Establish `h1 : ‖v i n‖ ≤ 1`. Simplify using `only [hv]`. Rewrite using `[norm_mul]`. Establish `h2 : ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1`.

Use `norm_cpow_neg_le_one' (hmemn n hn) ?_` and prove the remaining obligations. Simplify using `only [Complex.sub_re, Complex.ofReal_re]`. Combine the linear relations using `[(hT i hi).2.2.1]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, show 2 * U - U = U by omega]`. Establish `hoff : ∀ j ∈ T.erase i, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ 8 * Q ^ 3`. Introduce `j hj`. Take `⟨hji, hjT⟩` from `Finset.mem_erase.mp hj`.

Take `⟨hpi, hqi, hri1, hri2, himi, -⟩` from `hT i hi`. Take `⟨hpj, hqj, hrj1, hrj2, himj, -⟩` from `hT j hjT`. Use `set w : ℂ := (ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ)) with hw`. Establish `hsum : ∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n) = ∑ n ∈ Ioc U (2 * U), cv i n * (starRingEnd ℂ) (cv j n) * (n : ℂ) ^ (-w)`. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations.

Establish `hn0 : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (hmemn n hn).ne'`. Simplify using `only [hv, map_mul, conj_natCast_cpow_neg]`. Rewrite using `[hw, show -((ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ))) = -(ρ i - (s0 : ℂ)) + -(starRingEnd ℂ) (ρ j - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwre : w.re = (ρ i).re - s0 + ((ρ j).re - s0)`.

Simplify using `[hw, Complex.conj_re]`. Establish `hwim : w.im = (ρ i).im - (ρ j).im`. Simplify using `[hw, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwpos : 0 < w.re` using `by rw [hwre]; linarith`.

Establish `hne : i ≠ j` using `fun h => hji h.symm`. Rewrite using `[hsum]`. Use `(hPair i j hpi hpj hne w hwpos U hU).trans ?_` and prove the remaining obligations. Establish `hwn : ‖w‖ ≤ 1 + 2 * Q`. Use `(Complex.norm_le_abs_re_add_abs_im w).trans ?_` and prove the remaining obligations.

Establish `hre : |w.re| ≤ 1`. Rewrite using `[abs_le, hwre]`. Apply the tactic sequence `constructor <;> linarith`. Establish `him : |w.im| ≤ 2 * Q`. Rewrite using `[hwim]`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqq : (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) ≤ Q ^ 2`. Move the coercions through the operations in `at hqi hqj ⊢`. Rewrite using `[sq]`.

Conclude with `mul_le_mul hqi hqj (by positivity) hQ0.le`. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Q by linarith) (sq_nonneg Q)]`. Combine the equalities or inequalities in the displayed calculation. Use `add_le_add hdiag ?_` and prove the remaining obligations.

Use `Finset.sum_le_card_nsmul _ _ _ hoff` as an intermediate fact. Rewrite `this` using `[nsmul_eq_mul]`. Then use the resulting hypothesis. Use `_ ≤ Δ := by`. Rewrite using `[hΔ]`. Establish `hc : ((T.erase i).card : ℝ) ≤ T.card` using `by exact_mod_cast Finset.card_erase_le`.

Use polynomial arithmetic with `[pow_pos hQ0 3]`. Establish `hD` using `hDual PC ℕ T (Ioc U (2 * U)) b v Δ hΔ0 hrow`. Establish `hblk : ∀ i ∈ T, ∑ n ∈ Ioc U (2 * U), b n * v i n = blk Y N U i (ρ i)`. Introduce `i hi`. Unfold `blk`.

Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Establish `hn0 : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (hmemn n hn).ne'`. Simplify using `only [hb, hv]`. Rewrite using `[show -ρ i = -(s0 : ℂ) + -(ρ i - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ))`. Use `le_trans (le_of_eq ?_) (hL Y N U hU)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Simplify using `only [hb]`. Rewrite using `[norm_mul, Complex.norm_natCast_cpow_of_pos (hmemn n hn)]`.

Simplify using `only [Complex.neg_re, Complex.ofReal_re]`. Establish `hlow : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤ ∑ i ∈ T, ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2`. Use `Finset.card_nsmul_le_sum T (fun i => ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2) ((1 / (2 * (J : ℝ))) ^ 2) (fun i hi => by` as an intermediate fact. Rewrite using `[hblk i hi]`. Conclude with `pow_le_pow_left₀ (by positivity) (hT i hi).2.2.2.2.2 2)`.

Rewrite `this` using `[nsmul_eq_mul]`. Then use the resulting hypothesis. Establish `hup` using `hD.trans (mul_le_mul_of_nonneg_right hbn hΔ0)`. Establish `hUU : (U : ℝ) ^ (-(197 / 200 : ℝ)) * U = (U : ℝ) ^ (3 / 200 : ℝ)`. Rewrite using `[← Real.rpow_add_one hU0.ne']`. Evaluate the numerical expressions.

Establish `ht : (0 : ℝ) ≤ T.card` using `Nat.cast_nonneg _`. Establish `hsm : (T.card : ℝ) * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) ≤ T.card * (1 / (8 * (J : ℝ) ^ 2))`. Use `mul_le_mul_of_nonneg_left ?_ ht` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := hsmall`. Establish `key : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) + T.card * (1 / (8 * (J : ℝ) ^ 2))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hΔ]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := by`. Rewrite using `[hUU]`. Combine the linear relations using `[hsm]`. Establish `e1 : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 = 2 * ((T.card : ℝ) / (8 * (J : ℝ) ^ 2))`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (T.card : ℝ) * (1 / (8 * (J : ℝ) ^ 2)) = (T.card : ℝ) / (8 * (J : ℝ) ^ 2)`. Rewrite using `[mul_one_div]`. Rewrite `key` using `[e1, e2]`. Establish `h3 : (T.card : ℝ) / (8 * (J : ℝ) ^ 2) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ)` using `by linarith`.

Rewrite `h3` using `[div_le_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem blockCountOf_statement : BlockCountOf := by
  intro hDual hPair C hC hL Q hQ Y N U J hU hJ hsmall T ρ hT
  have hU0 : (0 : ℝ) < U := Nat.cast_pos.mpr (by omega)
  have hJ0 : (0 : ℝ) < J := Nat.cast_pos.mpr (by omega)
  have hs0 : s0 = 1 - 1 / 400 := rfl
  have hQ0 : (0 : ℝ) < Q := by linarith
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(s0 : ℂ)) with hb
  set v : PC → ℕ → ℂ := fun p n => cv p n * (n : ℂ) ^ (-(ρ p - (s0 : ℂ))) with hv
  set Δ : ℝ := (U : ℝ) + T.card * (8 * Q ^ 3) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hcv : ∀ p n, ‖cv p n‖ ≤ 1 := fun p n => DirichletCharacter.norm_le_one _ _
  have hmemn : ∀ n ∈ Ioc U (2 * U), 0 < n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hrow : ∀ i ∈ T, ∑ j ∈ T, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ := by
    intro i hi
    rw [← Finset.add_sum_erase T _ hi]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have hone : ∀ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ 1 := by
        intro n hn
        rw [norm_mul, RCLike.norm_conj]
        have h1 : ‖v i n‖ ≤ 1 := by
          simp only [hv]
          rw [norm_mul]
          have h2 : ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 := by
            refine norm_cpow_neg_le_one' (hmemn n hn) ?_
            simp only [Complex.sub_re, Complex.ofReal_re]
            linarith [(hT i hi).2.2.1]
          calc ‖cv i n‖ * ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 * 1 :=
                mul_le_mul (hcv i n) h2 (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        calc ‖v i n‖ * ‖v i n‖ ≤ 1 * 1 := mul_le_mul h1 h1 (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ∑ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ ∑ n ∈ Ioc U (2 * U), (1 : ℝ) :=
            Finset.sum_le_sum hone
        _ = U := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, show 2 * U - U = U by omega]
    have hoff : ∀ j ∈ T.erase i,
        ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ 8 * Q ^ 3 := by
      intro j hj
      obtain ⟨hji, hjT⟩ := Finset.mem_erase.mp hj
      obtain ⟨hpi, hqi, hri1, hri2, himi, -⟩ := hT i hi
      obtain ⟨hpj, hqj, hrj1, hrj2, himj, -⟩ := hT j hjT
      set w : ℂ := (ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ)) with hw
      have hsum : ∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n) =
          ∑ n ∈ Ioc U (2 * U), cv i n * (starRingEnd ℂ) (cv j n) * (n : ℂ) ^ (-w) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
        simp only [hv, map_mul, conj_natCast_cpow_neg]
        rw [hw, show -((ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ))) =
            -(ρ i - (s0 : ℂ)) + -(starRingEnd ℂ) (ρ j - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
        ring
      have hwre : w.re = (ρ i).re - s0 + ((ρ j).re - s0) := by
        simp [hw, Complex.conj_re]
      have hwim : w.im = (ρ i).im - (ρ j).im := by
        simp [hw, Complex.conj_im]
        ring
      have hwpos : 0 < w.re := by rw [hwre]; linarith
      have hne : i ≠ j := fun h => hji h.symm
      rw [hsum]
      refine (hPair i j hpi hpj hne w hwpos U hU).trans ?_
      have hwn : ‖w‖ ≤ 1 + 2 * Q := by
        refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
        have hre : |w.re| ≤ 1 := by
          rw [abs_le, hwre]
          constructor <;> linarith
        have him : |w.im| ≤ 2 * Q := by
          rw [hwim]
          calc |(ρ i).im - (ρ j).im| ≤ |(ρ i).im| + |(ρ j).im| := abs_sub _ _
            _ ≤ 2 * Q := by linarith
        linarith
      have hqq : (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) ≤ Q ^ 2 := by
        push_cast at hqi hqj ⊢
        rw [sq]
        exact mul_le_mul hqi hqj (by positivity) hQ0.le
      calc 2 * (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) * (1 + ‖w‖) ≤ 2 * Q ^ 2 * (2 + 2 * Q) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqq (by norm_num)) (by linarith)
              (by positivity) (by positivity)
        _ ≤ 8 * Q ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Q by linarith) (sq_nonneg Q)]
    calc ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ +
          ∑ j ∈ T.erase i, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖
        ≤ U + (T.erase i).card * (8 * Q ^ 3) := by
          refine add_le_add hdiag ?_
          have := Finset.sum_le_card_nsmul _ _ _ hoff
          rwa [nsmul_eq_mul] at this
      _ ≤ Δ := by
          rw [hΔ]
          have hc : ((T.erase i).card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_erase_le
          nlinarith [pow_pos hQ0 3]
  have hD := hDual PC ℕ T (Ioc U (2 * U)) b v Δ hΔ0 hrow
  have hblk : ∀ i ∈ T, ∑ n ∈ Ioc U (2 * U), b n * v i n = blk Y N U i (ρ i) := by
    intro i hi
    unfold blk
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
    simp only [hb, hv]
    rw [show -ρ i = -(s0 : ℂ) + -(ρ i - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
    ring
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
    refine le_trans (le_of_eq ?_) (hL Y N U hU)
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hb]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hmemn n hn)]
    simp only [Complex.neg_re, Complex.ofReal_re]
  have hlow : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      ∑ i ∈ T, ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2 := by
    have := Finset.card_nsmul_le_sum T (fun i => ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2)
      ((1 / (2 * (J : ℝ))) ^ 2) (fun i hi => by
        rw [hblk i hi]
        exact pow_le_pow_left₀ (by positivity) (hT i hi).2.2.2.2.2 2)
    rwa [nsmul_eq_mul] at this
  have hup := hD.trans (mul_le_mul_of_nonneg_right hbn hΔ0)
  have hUU : (U : ℝ) ^ (-(197 / 200 : ℝ)) * U = (U : ℝ) ^ (3 / 200 : ℝ) := by
    rw [← Real.rpow_add_one hU0.ne']
    norm_num
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hsm : (T.card : ℝ) * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) ≤
      T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ ht
    calc 8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ))) = 8 * Q ^ 3 * C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
          ring
      _ ≤ _ := hsmall
  have key : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      C * (U : ℝ) ^ (3 / 200 : ℝ) + T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    calc _ ≤ _ := hlow.trans hup
      _ = C * ((U : ℝ) ^ (-(197 / 200 : ℝ)) * U) +
            T.card * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) := by
          rw [hΔ]
          ring
      _ ≤ _ := by
          rw [hUU]
          linarith [hsm]
  have e1 : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 = 2 * ((T.card : ℝ) / (8 * (J : ℝ) ^ 2)) := by
    field_simp
    ring
  have e2 : (T.card : ℝ) * (1 / (8 * (J : ℝ) ^ 2)) = (T.card : ℝ) / (8 * (J : ℝ) ^ 2) := by
    rw [mul_one_div]
  rw [e1, e2] at key
  have h3 : (T.card : ℝ) / (8 * (J : ℝ) ^ 2) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) := by linarith
  rw [div_le_iff₀ (by positivity)] at h3
  calc (T.card : ℝ) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) * (8 * (J : ℝ) ^ 2) := h3
    _ = 8 * (J : ℝ) ^ 2 * C * (U : ℝ) ^ (3 / 200 : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
