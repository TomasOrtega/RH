import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hterm : ∀ i, ‖c i‖ ≤ 1 / ((idx i : ℝ) ^ (2 * ρ) * (idx i : ℝ) ^ 2)`. Introduce `i`. Establish `h1 : (1 : ℝ) ≤ idx i` using `by exact_mod_cast (le_trans (by norm_num) (h2 i))`. Use `(hcb i).trans ?_` and prove the remaining obligations. Establish `hn' : (4 * ρ + 4 : ℝ) ≤ n` using `by exact_mod_cast hn`.

Establish `hle : -(n : ℝ) / 2 ≤ -((2 * ρ + 2 : ℕ) : ℝ)` using `by push_cast; linarith`. Use `(Real.rpow_le_rpow_of_exponent_le h1 hle).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.rpow_neg (by linarith), Real.rpow_natCast, pow_add, one_div]`. Establish `hz` using `hasSum_zeta_two`. Establish `hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖c i‖ ≤ 0.65`.

Introduce `s`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image idx) (g := idx) (fun i hi => Finset.mem_image_of_mem _ hi)]`. Establish `hfib : ∀ m ∈ s.image idx, ∑ i ∈ s with idx i = m, ‖c i‖ ≤ 1 / (m : ℝ) ^ 2`. Introduce `m hm`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hm`.

Establish `hpos : (0 : ℝ) < idx j` using `by exact_mod_cast (lt_of_lt_of_le (by norm_num) (h2 j))`. Establish `hcard : ((s.filter (fun i => idx i = idx j)).card : ℝ) ≤ (idx j : ℝ) ^ (2 * ρ)`. Establish `h3 : (s.filter (fun i => idx i = idx j)).card ≤ {i | idx i = idx j}.ncard`. Rewrite using `[← Set.ncard_coe_finset]`. Use `Set.ncard_le_ncard ?_ (hc _).1` and prove the remaining obligations.

Introduce `i hi`. Simplify using `using (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2`. Conclude with `h3.trans (hc _).2` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_card_nsmul _ _ _ ?_` and prove the remaining obligations.

Introduce `i hi`. Use `hterm i` as an intermediate fact. Rewrite `this` using `[(Finset.mem_filter.1 hi).2]`. Then use the resulting hypothesis. Use `_ ≤ (idx j : ℝ) ^ (2 * ρ) * (1 / ((idx j : ℝ) ^ (2 * ρ) * (idx j : ℝ) ^ 2)) := by`. Rewrite using `[nsmul_eq_mul]`.

Conclude with `mul_le_mul_of_nonneg_right hcard (by positivity)`. Use `_ = 1 / (idx j : ℝ) ^ 2 := by field_simp`. Use `(Finset.sum_le_sum hfib).trans ?_` and prove the remaining obligations. Establish `h1 : 1 ∉ s.image idx`. Introduce `h`.

Take `⟨j, -, hj⟩` from `Finset.mem_image.1 h`. Use `h2 j` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h4` using `sum_le_hasSum (insert 1 (s.image idx)) (fun m _ => by positivity) hz`. Rewrite `h4` using `[Finset.sum_insert h1]`.

Establish `hpi` using `Real.pi_lt_d4`. Establish `hpi0` using `Real.pi_pos`. Establish `h5 : Real.pi ^ 2 ≤ 3.1416 ^ 2` using `by gcongr`. Evaluate the numerical expressions using `at h4 h5 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hs : Summable (fun i => ‖c i‖)` using `summable_of_sum_le (fun i => norm_nonneg _) hfin`. Conclude with `⟨hs, hs.tsum_le_of_sum_le hfin⟩`.
-/
theorem tail_sum_lt_one {ι : Type*} (idx : ι → ℕ) (ρ n : ℕ) (hn : 4 * ρ + 4 ≤ n) (h2 : ∀ i, 2 ≤ idx i)
    (hc : ∀ m, {i | idx i = m}.Finite ∧ {i | idx i = m}.ncard ≤ m ^ (2 * ρ)) (c : ι → ℂ) (hcb : ∀ i, ‖c i‖ ≤ (idx i : ℝ) ^ (-(n : ℝ) / 2)) :
    Summable (fun i => ‖c i‖) ∧ ∑' i, ‖c i‖ ≤ 0.65 := by
  classical
  have hterm : ∀ i, ‖c i‖ ≤ 1 / ((idx i : ℝ) ^ (2 * ρ) * (idx i : ℝ) ^ 2) := by
    intro i
    have h1 : (1 : ℝ) ≤ idx i := by exact_mod_cast (le_trans (by norm_num) (h2 i))
    refine (hcb i).trans ?_
    have hn' : (4 * ρ + 4 : ℝ) ≤ n := by exact_mod_cast hn
    have hle : -(n : ℝ) / 2 ≤ -((2 * ρ + 2 : ℕ) : ℝ) := by push_cast; linarith
    refine (Real.rpow_le_rpow_of_exponent_le h1 hle).trans (le_of_eq ?_)
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast, pow_add, one_div]
  have hz := hasSum_zeta_two
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖c i‖ ≤ 0.65 := by
    intro s
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image idx) (g := idx)
      (fun i hi => Finset.mem_image_of_mem _ hi)]
    have hfib : ∀ m ∈ s.image idx, ∑ i ∈ s with idx i = m, ‖c i‖ ≤ 1 / (m : ℝ) ^ 2 := by
      intro m hm
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hm
      have hpos : (0 : ℝ) < idx j := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (h2 j))
      have hcard : ((s.filter (fun i => idx i = idx j)).card : ℝ) ≤ (idx j : ℝ) ^ (2 * ρ) := by
        have h3 : (s.filter (fun i => idx i = idx j)).card ≤ {i | idx i = idx j}.ncard := by
          rw [← Set.ncard_coe_finset]
          refine Set.ncard_le_ncard ?_ (hc _).1
          intro i hi
          simpa using (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
        exact_mod_cast h3.trans (hc _).2
      calc ∑ i ∈ s with idx i = idx j, ‖c i‖
          ≤ (s.filter (fun i => idx i = idx j)).card •
              (1 / ((idx j : ℝ) ^ (2 * ρ) * (idx j : ℝ) ^ 2)) := by
            refine Finset.sum_le_card_nsmul _ _ _ ?_
            intro i hi
            have := hterm i
            rwa [(Finset.mem_filter.1 hi).2] at this
        _ ≤ (idx j : ℝ) ^ (2 * ρ) * (1 / ((idx j : ℝ) ^ (2 * ρ) * (idx j : ℝ) ^ 2)) := by
            rw [nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 1 / (idx j : ℝ) ^ 2 := by field_simp
    refine (Finset.sum_le_sum hfib).trans ?_
    have h1 : 1 ∉ s.image idx := by
      intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 h
      have := h2 j
      omega
    have h4 := sum_le_hasSum (insert 1 (s.image idx)) (fun m _ => by positivity) hz
    rw [Finset.sum_insert h1] at h4
    have hpi := Real.pi_lt_d4
    have hpi0 := Real.pi_pos
    have h5 : Real.pi ^ 2 ≤ 3.1416 ^ 2 := by gcongr
    norm_num at h4 h5 ⊢
    linarith
  have hs : Summable (fun i => ‖c i‖) := summable_of_sum_le (fun i => norm_nonneg _) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end GlobalTheory
