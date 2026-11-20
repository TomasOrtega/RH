import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronPsi

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.PerronCoeff
open GlobalTheory.PerronPsi

/- English proof (translation)
Take `⟨C, hC, hK⟩` from `kernel_bound`. Use `⟨480 * C, by positivity, ?_⟩` and prove the remaining obligations. Introduce `c u T hc hT hTu`. Establish `hu : 2 ≤ u` using `hT.trans hTu`. Establish `hu0 : 0 < u` using `by linarith`.

Establish `hT0 : 0 < T` using `by linarith`. Establish `hL : 1 / 2 ≤ Real.log u` using `half_le_log hu`. Establish `hL0 : 0 < Real.log u` using `by linarith`. Establish `hσ1 : 1 < 1 + 1 / Real.log u`. Establish `: 0 < 1 / Real.log u` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hσ0 : 0 < 1 + 1 / Real.log u` using `by linarith`. Establish `hc0 : c 0 = 0` using `by simpa using hc 0`. Establish `hs : LSeriesSummable c ((1 + 1 / Real.log u : ℝ) : ℂ)`. Establish `hΛ : LSeriesSummable (fun n => (Λ n : ℂ)) ((1 + 1 / Real.log u : ℝ) : ℂ)` using `ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ1)`.

Use `Summable.of_norm_bounded (hΛ.norm.mul_left 2) (fun n => ?_)` and prove the remaining obligations. Rewrite using `[LSeries.norm_term_eq, LSeries.norm_term_eq]`. Use `split_ifs with hn`. Simplify using the standard rewrite rules. Establish `hpow : 0 < (n : ℝ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ)).re`.

Establish `: (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn`. Check the signs of the components of the expression. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, mul_div_assoc']`. Conclude with `div_le_div_of_nonneg_right (hc n) hpow.le`. Establish `hI` using `interchange c hc0 T hσ0 hu0 hs`.

Establish `hS : HasSum (fun n : ℕ => c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0)) (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n)`. Establish `e : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n = ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0)`. Use `Finset.sum_congr rfl (fun n hn => ?_)` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Finset.mem_Icc.mp hn`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast h1`.

Establish `: 1 ≤ u / n`. Rewrite using `[le_div_iff₀ hn0, one_mul]`. Conclude with `(Nat.le_floor_iff hu0.le).mp h2`. Simplify using `[this]`. Rewrite using `[e]`.

Apply `hasSum_sum_of_ne_finset_zero` to reduce the goal to its premises. Introduce `n hn`. Break down `Nat.eq_zero_or_pos n with rfl | hpos` into its components or cases. Simplify using `[hc0]`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hpos`.

Establish `: ¬ (1 ≤ u / n)`. Introduce `h`. Apply `hn` to reduce the goal to its premises. Rewrite `h` using `[le_div_iff₀ hn0, one_mul]`. Conclude with `Finset.mem_Icc.mpr ⟨hpos, Nat.le_floor h⟩`.

Simplify using `[this]`. Establish `hD` using `hS.sub (hI.mul_left (1 / (2 * Real.pi) : ℂ))`. Establish `hfac : ∀ x y z v : ℂ, x * y - z * (x * v) = x * (y - z * v)` using `fun _ _ _ _ => by ring`. Establish `hp : 1 < 1 + 1 / (2 * Real.log u)`. Establish `: 0 < 1 / (2 * Real.log u)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsumm : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)))` using `Real.summable_one_div_nat_rpow.mpr hp`. Establish `hB : 0 ≤ 2 * u / T` using `by positivity`. Establish `hnear : HasSum (fun n : ℕ => if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0) (∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n)`. Establish `e : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n = ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0)` using `Finset.sum_congr rfl (fun n hn => by simp [hn])`.

Rewrite using `[e]`. Apply `hasSum_sum_of_ne_finset_zero` to reduce the goal to its premises. Introduce `n hn`. Simplify using `[hn]`. Establish `hg` using `(hsumm.hasSum.mul_left (2 * C * (12 * u * Real.log u / T))).add (hnear.mul_left (2 * C * (16 * Real.log u)))`.

Establish `hA0 : 0 ≤ 2 * C * (12 * u * Real.log u / T)` using `by positivity`. Establish `hBc0 : 0 ≤ 2 * C * (16 * Real.log u)` using `by positivity`. Establish `hbound` using `hD.norm_le_of_bounded hg (fun n => by`. Rewrite using `[hfac]`. Break down `Nat.eq_zero_or_pos n with rfl | hpos` into its components or cases.

Simplify using `only [hc0, zero_mul, norm_zero]`. Use `add_nonneg (mul_nonneg hA0 (by positivity)) (mul_nonneg hBc0 ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `w_nonneg _ hB _`. Conclude with `le_rfl`.

Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hpos`. Establish `hy : 0 < u / n` using `div_pos hu0 hn0`. Take `⟨hK1, hK2⟩` from `hK (u / n) (1 + 1 / Real.log u) T hy hσ0 (by linarith)`. Establish `hE0` using `norm_nonneg ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, ((u / n : ℝ) : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) - (if 1 ≤ u / n then 1 else 0))`. Rewrite using `[norm_mul, norm_sub_rev]`.

Establish `hcn : ‖c n‖ ≤ 2 * Real.log n` using `(hc n).trans (by linarith [ArithmeticFunction.vonMangoldt_le_log (n := n)])`. Establish `hmain` using `mul_le_mul_of_nonneg_right hcn hE0`. Establish `hfar0 : 0 ≤ 2 * C * (12 * u * Real.log u / T) * (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)))` using `mul_nonneg hA0 (by positivity)`. Distinguish the cases in `hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n`. Establish `h` using `far_term hu hT0 hpos hC.le hE0 hK2 hfar`.

Establish `hnr : 0 ≤ 2 * C * (16 * Real.log u) * (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0)`. Use `mul_nonneg hBc0 ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `w_nonneg _ hB _`. Conclude with `le_rfl`.

Use the polynomial consequences of the given equalities and inequalities. Use `push Not at hfar`. Establish `h` using `near_term hu hT0 hC.le hE0 hK1 hK2 hfar.1 hfar.2`. Establish `hmem : n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1))`. Rewrite using `[Finset.mem_range]`.

Establish `h1 : u < (⌊u⌋₊ : ℝ) + 1` using `Nat.lt_floor_add_one u`. Establish `h2 : (n : ℝ) < ((⌊u⌋₊ + 1 + (⌊u⌋₊ + 1) : ℕ) : ℝ)`. Use `push_cast`. Combine the linear relations using `[hfar.2]`. Conclude with `h2` after adjusting the coercions.

Rewrite using `[if_pos hmem]`. Use the proof step `nlinarith)`. Use `hbound.trans ?_` and prove the remaining obligations. Establish `hZ : ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)) ≤ 1 + 2 * Real.log u`. Establish `h` using `zeta_bound hp`.

Establish `e : 1 / (1 + 1 / (2 * Real.log u) - 1) = 2 * Real.log u`. Rewrite using `[add_sub_cancel_left, one_div_one_div]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `hN : Real.log ⌊u⌋₊ ≤ Real.log u`. Establish `hpos : (0 : ℝ) < ⌊u⌋₊`.

Establish `: 1 ≤ ⌊u⌋₊` using `Nat.le_floor (by norm_num; linarith)`. Conclude with `this` after adjusting the coercions. Conclude with `Real.log_le_log hpos (Nat.floor_le hu0.le)`. Establish `hW : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n ≤ 2 + 2 * u / T * (2 * (1 + Real.log u))`. Establish `h` using `sum_w ⌊u⌋₊ hB`.

Establish `: 2 * u / T * (2 * (1 + Real.log ⌊u⌋₊)) ≤ 2 * u / T * (2 * (1 + Real.log u))` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX : 0 ≤ u / T` using `by positivity`. Establish `hint : 0 ≤ (u / T) * Real.log u * (2 * Real.log u - 1)` using `mul_nonneg (mul_nonneg hX hL0.le) (by linarith)`. Establish `key : 2 * (12 * (u / T) * Real.log u) * (1 + 2 * Real.log u) + 2 * (16 * Real.log u) * (2 + 2 * (u / T) * (2 * (1 + Real.log u))) ≤ 480 * ((u / T) * Real.log u ^ 2 + Real.log u)`.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem truncated_perron_of_le_two_vonMangoldt : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (u T : ℝ), (∀ n, ‖c n‖ ≤ 2 * Λ n) → 2 ≤ T → T ≤ u → ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n) - (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, LSeries c (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)‖ ≤ C * (u * Real.log u ^ 2 / T + Real.log u) := by
  obtain ⟨C, hC, hK⟩ := kernel_bound
  refine ⟨480 * C, by positivity, ?_⟩
  intro c u T hc hT hTu
  have hu : 2 ≤ u := hT.trans hTu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1 / 2 ≤ Real.log u := half_le_log hu
  have hL0 : 0 < Real.log u := by linarith
  have hσ1 : 1 < 1 + 1 / Real.log u := by
    have : 0 < 1 / Real.log u := by positivity
    linarith
  have hσ0 : 0 < 1 + 1 / Real.log u := by linarith
  have hc0 : c 0 = 0 := by simpa using hc 0
  have hs : LSeriesSummable c ((1 + 1 / Real.log u : ℝ) : ℂ) := by
    have hΛ : LSeriesSummable (fun n => (Λ n : ℂ)) ((1 + 1 / Real.log u : ℝ) : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ1)
    refine Summable.of_norm_bounded (hΛ.norm.mul_left 2) (fun n => ?_)
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · simp
    · have hpow : 0 < (n : ℝ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ)).re := by
        have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
      rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        mul_div_assoc']
      exact div_le_div_of_nonneg_right (hc n) hpow.le
  have hI := interchange c hc0 T hσ0 hu0 hs
  have hS : HasSum (fun n : ℕ => c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n) := by
    have e : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n
        = ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
      have : 1 ≤ u / n := by
        rw [le_div_iff₀ hn0, one_mul]
        exact (Nat.le_floor_iff hu0.le).mp h2
      simp [this]
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [hc0]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
      have : ¬ (1 ≤ u / n) := by
        intro h
        apply hn
        rw [le_div_iff₀ hn0, one_mul] at h
        exact Finset.mem_Icc.mpr ⟨hpos, Nat.le_floor h⟩
      simp [this]
  have hD := hS.sub (hI.mul_left (1 / (2 * Real.pi) : ℂ))
  have hfac : ∀ x y z v : ℂ, x * y - z * (x * v) = x * (y - z * v) := fun _ _ _ _ => by ring
  have hp : 1 < 1 + 1 / (2 * Real.log u) := by
    have : 0 < 1 / (2 * Real.log u) := by positivity
    linarith
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hB : 0 ≤ 2 * u / T := by positivity
  have hnear : HasSum (fun n : ℕ =>
        if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0)
      (∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n) := by
    have e : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
        = ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)),
          (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0) :=
      Finset.sum_congr rfl (fun n hn => by simp [hn])
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp [hn]
  have hg := (hsumm.hasSum.mul_left (2 * C * (12 * u * Real.log u / T))).add
    (hnear.mul_left (2 * C * (16 * Real.log u)))
  have hA0 : 0 ≤ 2 * C * (12 * u * Real.log u / T) := by positivity
  have hBc0 : 0 ≤ 2 * C * (16 * Real.log u) := by positivity
  have hbound := hD.norm_le_of_bounded hg (fun n => by
    rw [hfac]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [hc0, zero_mul, norm_zero]
      refine add_nonneg (mul_nonneg hA0 (by positivity)) (mul_nonneg hBc0 ?_)
      split_ifs
      · exact w_nonneg _ hB _
      · exact le_rfl
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have hy : 0 < u / n := div_pos hu0 hn0
    obtain ⟨hK1, hK2⟩ := hK (u / n) (1 + 1 / Real.log u) T hy hσ0 (by linarith)
    have hE0 := norm_nonneg ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        ((u / n : ℝ) : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)
          / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) - (if 1 ≤ u / n then 1 else 0))
    rw [norm_mul, norm_sub_rev]
    have hcn : ‖c n‖ ≤ 2 * Real.log n :=
      (hc n).trans (by linarith [ArithmeticFunction.vonMangoldt_le_log (n := n)])
    have hmain := mul_le_mul_of_nonneg_right hcn hE0
    have hfar0 : 0 ≤ 2 * C * (12 * u * Real.log u / T)
        * (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))) := mul_nonneg hA0 (by positivity)
    by_cases hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n
    · have h := far_term hu hT0 hpos hC.le hE0 hK2 hfar
      have hnr : 0 ≤ 2 * C * (16 * Real.log u)
          * (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0) := by
        refine mul_nonneg hBc0 ?_
        split_ifs
        · exact w_nonneg _ hB _
        · exact le_rfl
      nlinarith
    · push Not at hfar
      have h := near_term hu hT0 hC.le hE0 hK1 hK2 hfar.1 hfar.2
      have hmem : n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) := by
        rw [Finset.mem_range]
        have h1 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
        have h2 : (n : ℝ) < ((⌊u⌋₊ + 1 + (⌊u⌋₊ + 1) : ℕ) : ℝ) := by
          push_cast
          linarith [hfar.2]
        exact_mod_cast h2
      rw [if_pos hmem]
      nlinarith)
  refine hbound.trans ?_
  have hZ : ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)) ≤ 1 + 2 * Real.log u := by
    have h := zeta_bound hp
    have e : 1 / (1 + 1 / (2 * Real.log u) - 1) = 2 * Real.log u := by
      rw [add_sub_cancel_left, one_div_one_div]
    rwa [e] at h
  have hN : Real.log ⌊u⌋₊ ≤ Real.log u := by
    have hpos : (0 : ℝ) < ⌊u⌋₊ := by
      have : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by norm_num; linarith)
      exact_mod_cast this
    exact Real.log_le_log hpos (Nat.floor_le hu0.le)
  have hW : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
      ≤ 2 + 2 * u / T * (2 * (1 + Real.log u)) := by
    have h := sum_w ⌊u⌋₊ hB
    have : 2 * u / T * (2 * (1 + Real.log ⌊u⌋₊)) ≤ 2 * u / T * (2 * (1 + Real.log u)) := by
      gcongr
    linarith
  have hX : 0 ≤ u / T := by positivity
  have hint : 0 ≤ (u / T) * Real.log u * (2 * Real.log u - 1) :=
    mul_nonneg (mul_nonneg hX hL0.le) (by linarith)
  have key : 2 * (12 * (u / T) * Real.log u) * (1 + 2 * Real.log u)
      + 2 * (16 * Real.log u) * (2 + 2 * (u / T) * (2 * (1 + Real.log u)))
      ≤ 480 * ((u / T) * Real.log u ^ 2 + Real.log u) := by
    nlinarith
  calc 2 * C * (12 * u * Real.log u / T) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))
        + 2 * C * (16 * Real.log u)
          * ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
      ≤ 2 * C * (12 * u * Real.log u / T) * (1 + 2 * Real.log u)
        + 2 * C * (16 * Real.log u) * (2 + 2 * u / T * (2 * (1 + Real.log u))) := by
        gcongr
    _ = C * (2 * (12 * (u / T) * Real.log u) * (1 + 2 * Real.log u)
        + 2 * (16 * Real.log u) * (2 + 2 * (u / T) * (2 * (1 + Real.log u)))) := by ring
    _ ≤ C * (480 * ((u / T) * Real.log u ^ 2 + Real.log u)) :=
        mul_le_mul_of_nonneg_left key hC.le
    _ = 480 * C * (u * Real.log u ^ 2 / T + Real.log u) := by ring

end GlobalTheory.PerronCoeff
