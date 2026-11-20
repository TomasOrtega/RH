import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine

namespace ReciprocityTheory.ChartRestriction.G.FD

open Finset

/- English proof (translation)
Establish `hK0 : 0 < K` using `by linarith`. Establish `hN0 : 0 < N` using `by linarith`. Establish `hL : 0 ≤ Real.log (2 * K * N)` using `Real.log_nonneg (by nlinarith)`. Establish `hNL : 0 ≤ N * Real.log (2 * K * N)` using `mul_nonneg hN0.le hL`. Establish `hm0 : 0 < m` using `by linarith`.

Establish `hKm : 0 < K * m` using `mul_pos hK0 hm0`. Establish `h1 : Real.log (K * m) = Real.log (2 * K * N) + Real.log (m / (2 * N))`. Rewrite using `[← Real.log_mul (by positivity) (by positivity)]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Establish `h2 : Real.log (m / (2 * N)) ≤ m / (2 * N) - 1` using `Real.log_le_sub_one_of_pos (by positivity)`. Establish `h3 : N * (m / (2 * N)) = m / 2`. Clear the denominators using the available nonvanishing facts. Establish `h4` using `mul_le_mul_of_nonneg_left h2 hN0.le`. Rewrite using `[Real.rpow_def_of_pos hKm]`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[h1]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pow_le_exp_of_log_bound {K N w m : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hw : 0 ≤ w)
    (hm : w + N * Real.log (2 * K * N) + N + 2 ≤ m) :
    (K * m) ^ N ≤ Real.exp (2 * m - w - 2) := by
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log (2 * K * N) := Real.log_nonneg (by nlinarith)
  have hNL : 0 ≤ N * Real.log (2 * K * N) := mul_nonneg hN0.le hL
  have hm0 : 0 < m := by linarith
  have hKm : 0 < K * m := mul_pos hK0 hm0
  have h1 : Real.log (K * m) = Real.log (2 * K * N) + Real.log (m / (2 * N)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (m / (2 * N)) ≤ m / (2 * N) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : N * (m / (2 * N)) = m / 2 := by
    field_simp
  have h4 := mul_le_mul_of_nonneg_left h2 hN0.le
  rw [Real.rpow_def_of_pos hKm]
  apply Real.exp_le_exp.mpr
  rw [h1]
  nlinarith

/- English proof (translation)
Introduce `K N w hK hN hw ι t ht hcount`. Establish `hK0 : 0 < K` using `by linarith`. Establish `hN0 : 0 < N` using `by linarith`. Establish `hL : 0 ≤ Real.log (2 * K * N)` using `Real.log_nonneg (by nlinarith)`. Establish `hNL : 0 ≤ N * Real.log (2 * K * N)` using `mul_nonneg hN0.le hL`.

Establish `ht3 : ∀ j, 3 < t j` using `fun j => by linarith [ht j]`. Establish `hpi` using `Real.pi_gt_three`. Use `set q : ℝ := Real.exp (2 - Real.pi) with hq`. Establish `hq0 : 0 ≤ q` using `(Real.exp_pos _).le`. Establish `hq1 : q < Real.exp (-1)` using `Real.exp_lt_exp.mpr (by linarith)`.

Establish `he1 : Real.exp (-1) < 1 / 2`. Establish `h2 : 2 < Real.exp 1` using `by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]`. Rewrite using `[Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq12 : q < 1 / 2` using `lt_trans hq1 he1`.

Establish `hbound : ∀ s : Finset ι, ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q))`. Introduce `s`. Take `⟨mj, hmj⟩ : ∃ mj : ι → ℕ, mj = fun j => ⌈t j⌉₊` from `⟨_, rfl⟩`. Establish `hmj_ge : ∀ j, t j ≤ (mj j : ℝ)` using `fun j => by rw [hmj]; exact Nat.le_ceil _`. Establish `hmj_lt : ∀ j, (mj j : ℝ) < t j + 1` using `fun j => by`.

Rewrite using `[hmj]; exact Nat.ceil_lt_add_one (by linarith [ht3 j])`. Establish `hmj4 : ∀ j, 4 ≤ mj j` using `fun j => by`. Establish `h1 : (3 : ℝ) < mj j` using `lt_of_lt_of_le (ht3 j) (hmj_ge j)`. Establish `h2 : (3 : ℕ) < mj j` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers.

Establish `step1 : ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ ∑ j ∈ s, Real.exp (-Real.pi * ((mj j : ℝ) - 1))` using `Finset.sum_le_sum (fun j _ => Real.exp_le_exp.mpr (by have := hmj_lt j; nlinarith [Real.pi_pos]))`. Establish `step2 : ∀ y ∈ s.image mj, ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) ≤ Real.exp (Real.pi - w - 2) * q ^ y`. Introduce `y hy`. Take `⟨j0, _, hj0y⟩` from `Finset.mem_image.mp hy`. Establish `hyT : w + N * Real.log (2 * K * N) + N + 2 ≤ (y : ℝ)`.

Rewrite using `[← hj0y]`. Combine the linear relations using `[ht j0, hmj_ge j0]`. Establish `hy1 : (1 : ℝ) ≤ y` using `by linarith`. Establish `hsum : ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) = ((s.filter (fun j => mj j = y)).card : ℝ) * Real.exp (-Real.pi * ((y : ℝ) - 1))`. Rewrite using `[Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.sum_const, nsmul_eq_mul]`.

Establish `hcard : ((s.filter (fun j => mj j = y)).card : ℝ) ≤ Real.exp (2 * y - w - 2)`. Take `⟨hfin, hle⟩` from `hcount y hy1`. Establish `hsub : ((s.filter (fun j => mj j = y) : Finset ι) : Set ι) ⊆ {j | t j ≤ (y : ℝ)}`. Introduce `j hj`. Establish `hj'` using `Finset.mem_filter.mp hj`.

Use `show t j ≤ (y : ℝ)`. Rewrite using `[← hj'.2]`. Conclude with `hmj_ge j`. Establish `h1 : (s.filter (fun j => mj j = y)).card ≤ {j | t j ≤ (y : ℝ)}.ncard`. Rewrite using `[← Set.ncard_coe_finset]`.

Conclude with `Set.ncard_le_ncard hsub hfin`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h1` after adjusting the coercions. Use `_ ≤ (K * y) ^ N := hle`. Use `_ ≤ Real.exp (2 * y - w - 2) := pow_le_exp_of_log_bound hK hN hw hyT`.

Rewrite using `[hsum]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `step3 : ∑ y ∈ s.image mj, Real.exp (Real.pi - w - 2) * q ^ y ≤ Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q))`. Rewrite using `[← Finset.mul_sum]`. Apply `mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises.

Introduce `y hy`. Take `⟨j, hj, rfl⟩` from `Finset.mem_image.mp hy`. Rewrite using `[Finset.mem_Ico]`. Conclude with `⟨hmj4 j, Nat.lt_succ_of_le (Finset.le_sup hj)⟩`. Introduce `y _ _`.

Conclude with `pow_nonneg hq0 y`. Use `_ ≤ q ^ 4 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Establish `hnn : ∀ j, 0 ≤ Real.exp (-Real.pi * t j)` using `fun j => (Real.exp_pos _).le`. Establish `hsumm : Summable (fun j => Real.exp (-Real.pi * t j))` using `summable_of_sum_le hnn hbound`.

Use `⟨hsumm, ?_⟩` and prove the remaining obligations. Establish `htsum : ∑' j, Real.exp (-Real.pi * t j) ≤ Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q))` using `hsumm.tsum_le_of_sum_le hbound`. Establish `h2w : (2 : ℝ) ^ (w / 2) ≤ Real.exp w`. Rewrite using `[Real.rpow_def_of_pos (by norm_num)]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Establish `h1 : Real.log 2 < 2` using `by linarith [Real.log_two_lt_d9]`. Use polynomial arithmetic with `[Real.log_pos (show (1 : ℝ) < 2 by norm_num)]`. Establish `hq4 : q ^ 4 = Real.exp (8 - 4 * Real.pi)`. Rewrite using `[hq, ← Real.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < 1 - q` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hq4, show Real.exp (6 - 3 * Real.pi) = Real.exp w * (Real.exp (Real.pi - w - 2) * Real.exp (8 - 4 * Real.pi)) by`.

Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Use the proof step `ring]`. Expand and normalize the polynomial expressions, which then agree. Use `_ < 1 / 2 := by`.

Establish `h4 : Real.exp (6 - 3 * Real.pi) < Real.exp (-3)` using `Real.exp_lt_exp.mpr (by linarith)`. Establish `h5 : 4 < Real.exp 3` using `by linarith [Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)]`. Establish `h7 : Real.exp (-3) < 1 / 4`. Rewrite using `[Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 3) (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[div_lt_div_iff₀ hpos (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem counting_exponential_sum_holds : CountingExponentialSum := by
  intro K N w hK hN hw ι t ht hcount
  classical
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log (2 * K * N) := Real.log_nonneg (by nlinarith)
  have hNL : 0 ≤ N * Real.log (2 * K * N) := mul_nonneg hN0.le hL
  have ht3 : ∀ j, 3 < t j := fun j => by linarith [ht j]
  have hpi := Real.pi_gt_three
  set q : ℝ := Real.exp (2 - Real.pi) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < Real.exp (-1) := Real.exp_lt_exp.mpr (by linarith)
  have he1 : Real.exp (-1) < 1 / 2 := by
    have h2 : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
    rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hq12 : q < 1 / 2 := lt_trans hq1 he1
  have hbound : ∀ s : Finset ι, ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤
      Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) := by
    intro s
    obtain ⟨mj, hmj⟩ : ∃ mj : ι → ℕ, mj = fun j => ⌈t j⌉₊ := ⟨_, rfl⟩
    have hmj_ge : ∀ j, t j ≤ (mj j : ℝ) := fun j => by rw [hmj]; exact Nat.le_ceil _
    have hmj_lt : ∀ j, (mj j : ℝ) < t j + 1 := fun j => by
      rw [hmj]; exact Nat.ceil_lt_add_one (by linarith [ht3 j])
    have hmj4 : ∀ j, 4 ≤ mj j := fun j => by
      have h1 : (3 : ℝ) < mj j := lt_of_lt_of_le (ht3 j) (hmj_ge j)
      have h2 : (3 : ℕ) < mj j := by exact_mod_cast h1
      omega
    have step1 : ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ ∑ j ∈ s, Real.exp (-Real.pi * ((mj j : ℝ) - 1)) :=
      Finset.sum_le_sum (fun j _ => Real.exp_le_exp.mpr (by have := hmj_lt j; nlinarith [Real.pi_pos]))
    have step2 : ∀ y ∈ s.image mj, ∑ j ∈ s.filter (fun j => mj j = y),
        Real.exp (-Real.pi * ((mj j : ℝ) - 1)) ≤ Real.exp (Real.pi - w - 2) * q ^ y := by
      intro y hy
      obtain ⟨j0, _, hj0y⟩ := Finset.mem_image.mp hy
      have hyT : w + N * Real.log (2 * K * N) + N + 2 ≤ (y : ℝ) := by
        rw [← hj0y]; linarith [ht j0, hmj_ge j0]
      have hy1 : (1 : ℝ) ≤ y := by linarith
      have hsum : ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) =
          ((s.filter (fun j => mj j = y)).card : ℝ) * Real.exp (-Real.pi * ((y : ℝ) - 1)) := by
        rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.sum_const,
          nsmul_eq_mul]
      have hcard : ((s.filter (fun j => mj j = y)).card : ℝ) ≤ Real.exp (2 * y - w - 2) := by
        obtain ⟨hfin, hle⟩ := hcount y hy1
        have hsub : ((s.filter (fun j => mj j = y) : Finset ι) : Set ι) ⊆ {j | t j ≤ (y : ℝ)} := by
          intro j hj
          have hj' := Finset.mem_filter.mp hj
          show t j ≤ (y : ℝ)
          rw [← hj'.2]
          exact hmj_ge j
        have h1 : (s.filter (fun j => mj j = y)).card ≤ {j | t j ≤ (y : ℝ)}.ncard := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard hsub hfin
        calc ((s.filter (fun j => mj j = y)).card : ℝ) ≤ ({j | t j ≤ (y : ℝ)}.ncard : ℝ) := by
              exact_mod_cast h1
          _ ≤ (K * y) ^ N := hle
          _ ≤ Real.exp (2 * y - w - 2) := pow_le_exp_of_log_bound hK hN hw hyT
      rw [hsum]
      calc ((s.filter (fun j => mj j = y)).card : ℝ) * Real.exp (-Real.pi * ((y : ℝ) - 1))
          ≤ Real.exp (2 * y - w - 2) * Real.exp (-Real.pi * ((y : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
        _ = Real.exp (Real.pi - w - 2) * q ^ y := by
            rw [hq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
    have step3 : ∑ y ∈ s.image mj, Real.exp (Real.pi - w - 2) * q ^ y ≤
        Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      calc ∑ y ∈ s.image mj, q ^ y ≤ ∑ y ∈ Finset.Ico 4 (s.sup mj + 1), q ^ y := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro y hy
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
              rw [Finset.mem_Ico]
              exact ⟨hmj4 j, Nat.lt_succ_of_le (Finset.le_sup hj)⟩
            · intro y _ _
              exact pow_nonneg hq0 y
        _ ≤ q ^ 4 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 (by linarith)
    calc ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ ∑ j ∈ s, Real.exp (-Real.pi * ((mj j : ℝ) - 1)) := step1
      _ = ∑ y ∈ s.image mj, ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) :=
          (Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem mj hj) _).symm
      _ ≤ ∑ y ∈ s.image mj, Real.exp (Real.pi - w - 2) * q ^ y := Finset.sum_le_sum step2
      _ ≤ _ := step3
  have hnn : ∀ j, 0 ≤ Real.exp (-Real.pi * t j) := fun j => (Real.exp_pos _).le
  have hsumm : Summable (fun j => Real.exp (-Real.pi * t j)) := summable_of_sum_le hnn hbound
  refine ⟨hsumm, ?_⟩
  have htsum : ∑' j, Real.exp (-Real.pi * t j) ≤ Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) :=
    hsumm.tsum_le_of_sum_le hbound
  have h2w : (2 : ℝ) ^ (w / 2) ≤ Real.exp w := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have h1 : Real.log 2 < 2 := by linarith [Real.log_two_lt_d9]
    nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  have hq4 : q ^ 4 = Real.exp (8 - 4 * Real.pi) := by
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpos : 0 < 1 - q := by linarith
  calc (2 : ℝ) ^ (w / 2) * ∑' j, Real.exp (-Real.pi * t j)
      ≤ Real.exp w * (Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q))) :=
        mul_le_mul h2w htsum (tsum_nonneg hnn) (Real.exp_pos _).le
    _ = Real.exp (6 - 3 * Real.pi) / (1 - q) := by
        rw [hq4, show Real.exp (6 - 3 * Real.pi) =
          Real.exp w * (Real.exp (Real.pi - w - 2) * Real.exp (8 - 4 * Real.pi)) by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring]
        ring
    _ < 1 / 2 := by
        have h4 : Real.exp (6 - 3 * Real.pi) < Real.exp (-3) := Real.exp_lt_exp.mpr (by linarith)
        have h5 : 4 < Real.exp 3 := by linarith [Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)]
        have h7 : Real.exp (-3) < 1 / 4 := by
          rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 3) (by norm_num)]
          linarith
        rw [div_lt_div_iff₀ hpos (by norm_num)]
        linarith

end ReciprocityTheory.ChartRestriction.G.FD
