import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsMore
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.GoodHeight

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hn : (0 : ℝ) < (S.card : ℝ) + 1` using `by positivity`. Establish `key : ∀ k ∈ Finset.range (S.card + 1), ∃ x ∈ S, |x - (T + (k : ℝ) / ((S.card : ℝ) + 1))| < 1 / (2 * ((S.card : ℝ) + 1))`. Introduce `k hk`.

Establish `hk' : (k : ℝ) ≤ S.card`. Conclude with `Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)` after adjusting the coercions. Apply `hcon` to reduce the goal to its premises. Establish `: 0 ≤ (k : ℝ) / ((S.card : ℝ) + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: (k : ℝ) / ((S.card : ℝ) + 1) ≤ 1`. Rewrite using `[div_le_one hn]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Use `choose! g hgS hg using key`.

Take `⟨a, ha, b, hb, hab, heq⟩` from `Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (S.card + 1)) (t := S) (by simp) (fun k hk => hgS k hk)`. Establish `h1` using `hg a ha`. Establish `h2` using `hg b hb`. Rewrite `h1` using `[heq]`. Establish `hclose : |(a : ℝ) / ((S.card : ℝ) + 1) - (b : ℝ) / ((S.card : ℝ) + 1)| < 1 / ((S.card : ℝ) + 1)`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ |g b - (T + (b : ℝ) / ((S.card : ℝ) + 1))| + |g b - (T + (a : ℝ) / ((S.card : ℝ) + 1))| := abs_sub _ _`. Use `_ < 1 / (2 * ((S.card : ℝ) + 1)) + 1 / (2 * ((S.card : ℝ) + 1)) := add_lt_add h2 h1`.

Use `_ = 1 / ((S.card : ℝ) + 1) := by field_simp; ring`. Rewrite `hclose` using `[← sub_div, abs_div, abs_of_pos hn, div_lt_div_iff_of_pos_right hn]`. Establish `hsep : (1 : ℝ) ≤ |(a : ℝ) - b|`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Establish `: (a : ℝ) + 1 ≤ b` using `by exact_mod_cast h`.

Rewrite using `[abs_sub_comm, abs_of_nonneg (by linarith)]; linarith`. Establish `: (b : ℝ) + 1 ≤ a` using `by exact_mod_cast h`. Rewrite using `[abs_of_nonneg (by linarith)]; linarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_far (S : Finset ℝ) (T : ℝ) : ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
    ∀ x ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |x - T'| := by
  classical
  by_contra hcon
  push Not at hcon
  have hn : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have key : ∀ k ∈ Finset.range (S.card + 1), ∃ x ∈ S,
      |x - (T + (k : ℝ) / ((S.card : ℝ) + 1))| < 1 / (2 * ((S.card : ℝ) + 1)) := by
    intro k hk
    have hk' : (k : ℝ) ≤ S.card := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    apply hcon
    · have : 0 ≤ (k : ℝ) / ((S.card : ℝ) + 1) := by positivity
      linarith
    · have : (k : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hn]; linarith
      linarith
  choose! g hgS hg using key
  obtain ⟨a, ha, b, hb, hab, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (S.card + 1)) (t := S)
      (by simp) (fun k hk => hgS k hk)
  have h1 := hg a ha
  have h2 := hg b hb
  rw [heq] at h1
  have hclose : |(a : ℝ) / ((S.card : ℝ) + 1) - (b : ℝ) / ((S.card : ℝ) + 1)|
      < 1 / ((S.card : ℝ) + 1) := by
    calc |(a : ℝ) / ((S.card : ℝ) + 1) - (b : ℝ) / ((S.card : ℝ) + 1)|
        = |(g b - (T + (b : ℝ) / ((S.card : ℝ) + 1))) - (g b - (T + (a : ℝ) / ((S.card : ℝ) + 1)))| := by
          congr 1; ring
      _ ≤ |g b - (T + (b : ℝ) / ((S.card : ℝ) + 1))| + |g b - (T + (a : ℝ) / ((S.card : ℝ) + 1))| :=
          abs_sub _ _
      _ < 1 / (2 * ((S.card : ℝ) + 1)) + 1 / (2 * ((S.card : ℝ) + 1)) := add_lt_add h2 h1
      _ = 1 / ((S.card : ℝ) + 1) := by field_simp; ring
  rw [← sub_div, abs_div, abs_of_pos hn, div_lt_div_iff_of_pos_right hn] at hclose
  have hsep : (1 : ℝ) ≤ |(a : ℝ) - b| := by
    rcases lt_or_gt_of_ne hab with h | h
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  linarith

/- English proof (translation)
Establish `hU : IsPreconnected ({1}ᶜ : Set ℂ)` using `(isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected`. Establish `han : AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ)`. Introduce `z hz`. Establish `hd : DifferentiableOn ℂ (LFunction χ) ({1}ᶜ : Set ℂ)` using `fun u hu => (differentiableAt_LFunction χ u (.inl hu)).differentiableWithinAt`. Conclude with `hd.analyticAt (isOpen_compl_singleton.mem_nhds hz)`.

Establish `h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)` using `by norm_num`. Establish `hw1 : w ∈ ({1}ᶜ : Set ℂ)` using `h1`. Establish `hne2 : analyticOrderAt (LFunction χ) 2 ≠ ⊤`. Rewrite using `[(han 2 h2).analyticOrderAt_eq_zero.mpr (LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num))]`. Conclude with `ENat.zero_ne_top`.

Establish `hnetop` using `han.analyticOrderAt_ne_top_of_isPreconnected hU h2 hw1 hne2`. Establish `hne0 : analyticOrderAt (LFunction χ) w ≠ 0` using `(han w hw1).analyticOrderAt_ne_zero.mpr hw`. Unfold `analyticOrderNatAt`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp hnetop`. Rewrite `hne0`, the goal using `[← hn]`.

Simplify using `only [ENat.toNat_natCast]`. Establish `: n ≠ 0` using `by rintro rfl; exact hne0 rfl`. Use linear arithmetic over natural numbers and integers.
-/
theorem one_le_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {w : ℂ} (h1 : w ≠ 1)
    (hw : LFunction χ w = 0) : 1 ≤ analyticOrderNatAt (LFunction χ) w := by
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have han : AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := by
    intro z hz
    have hd : DifferentiableOn ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := fun u hu =>
      (differentiableAt_LFunction χ u (.inl hu)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hz)
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hw1 : w ∈ ({1}ᶜ : Set ℂ) := h1
  have hne2 : analyticOrderAt (LFunction χ) 2 ≠ ⊤ := by
    rw [(han 2 h2).analyticOrderAt_eq_zero.mpr
      (LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num))]
    exact ENat.zero_ne_top
  have hnetop := han.analyticOrderAt_ne_top_of_isPreconnected hU h2 hw1 hne2
  have hne0 : analyticOrderAt (LFunction χ) w ≠ 0 := (han w hw1).analyticOrderAt_ne_zero.mpr hw
  unfold analyticOrderNatAt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_natCast]
  have : n ≠ 0 := by rintro rfl; exact hne0 rfl
  omega

/- English proof (translation)
Use `⟨∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩` and prove the remaining obligations. Introduce `N _ χ s hs`. Establish `hs1 : 1 < s.re` using `by linarith`. Establish `hsum2 : Summable (fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖)` using `summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by norm_num))`. Establish `key` using `LSeries_twist_vonMangoldt_eq χ hs1`.

Rewrite `key` using `[← LFunction_eq_LSeries χ hs1, ← deriv_LFunction_eq_deriv_LSeries χ hs1]`. Rewrite using `[← neg_neg (deriv (LFunction χ) s / LFunction χ s), ← neg_div, ← key, norm_neg]`. Unfold `LSeries`. Use `(norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun n => ?_) ?_ hsum2)` and prove the remaining obligations. Conclude with `summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs1)`.

Use `(LSeries.norm_term_le_of_re_le_re _ (show (2 : ℂ).re ≤ s.re by simpa using hs) n).trans (LSeries.norm_term_le 2 ?_)` and prove the remaining obligations. Simplify using `only [Pi.mul_apply, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)`. Conclude with `summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs1)`.
-/
theorem exists_bound_right : ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ), 2 ≤ s.re → ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ B := by
  refine ⟨∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro N _ χ s hs
  have hs1 : 1 < s.re := by linarith
  have hsum2 : Summable (fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by norm_num))
  have key := LSeries_twist_vonMangoldt_eq χ hs1
  rw [← LFunction_eq_LSeries χ hs1, ← deriv_LFunction_eq_deriv_LSeries χ hs1] at key
  rw [← neg_neg (deriv (LFunction χ) s / LFunction χ s), ← neg_div, ← key, norm_neg]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun n => ?_) ?_ hsum2)
  · exact summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs1)
  · refine (LSeries.norm_term_le_of_re_le_re _ (show (2 : ℂ).re ≤ s.re by simpa using hs) n).trans
      (LSeries.norm_term_le 2 ?_)
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  · exact summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs1)

/- English proof (translation)
Take `⟨C₁, hC₁, h₁⟩` from `GlobalTheory.LWide.logDeriv_LFunction_strip`. Take `⟨C₂, hC₂, h₂⟩` from `GlobalTheory.ZetaWide.main`. Use `⟨C₁ + C₂ + 1, by positivity, ?_⟩` and prove the remaining obligations. Introduce `N _ χ hprim s hs1 hs2 ht hLs`. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`.

Establish `hlog : 1 ≤ Real.log (N * (|s.im| + 2))`. Rewrite using `[Real.le_log_iff_exp_le (by positivity)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Distinguish the cases in `hχ : χ = 1`.

Establish `hN : N = 1`. Establish `h` using `hprim`. Rewrite `h` using `[DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one]`. Conclude with `h.symm`. Substitute `hN` using the available equality.

Simplify using `only [LFunction_modOne_eq] at hLs ⊢`. Simplify using `only [Nat.cast_one, one_mul] at hlog ⊢`. Establish `hs1' : s ≠ 1`. Introduce and unpack `rfl`. Evaluate the numerical expressions using `at ht`.

Take `⟨hfin, hcount, hbound⟩` from `h₂ s hs1 hs2 hs1' hLs`. Rewrite `hcount`, `hbound` using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`. Use `⟨hfin.toFinset, fun w => by simp, ?_, ?_⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Establish `hinv : ‖1 / (s - 1)‖ ≤ 1 / 2`.

Establish `h : 2 ≤ ‖s - 1‖` using `le_trans ht (by simpa using Complex.abs_im_le_norm (s - 1))`. Rewrite using `[norm_div, norm_one]`. Conclude with `one_div_le_one_div_of_le (by norm_num) h`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _`. Use `_ ≤ C₂ * Real.log (|s.im| + 2) + 1 / 2 := add_le_add hbound hinv`. Use `_ ≤ (C₁ + C₂ + 1) * Real.log (|s.im| + 2) := by nlinarith`. Take `⟨hfin, hcount, hbound⟩` from `h₁ N χ hχ s hs1 hs2 hLs`.

Rewrite `hcount`, `hbound` using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`. Use `⟨hfin.toFinset, fun w => ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, fun h => LFunction_apply_one_ne_zero hχ (h ▸ h2), h2⟩`. Introduce and unpack `⟨h1, -, h2⟩`. Conclude with `⟨h1, h2⟩`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem local_formula : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → LFunction χ s ≠ 0 →
    ∃ Z : Finset ℂ, (∀ w, w ∈ Z ↔ ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ LFunction χ w = 0) ∧
      ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℝ) ≤ C * Real.log (N * (|s.im| + 2)) ∧
      ‖deriv (LFunction χ) s / LFunction χ s
        - ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖
        ≤ C * Real.log (N * (|s.im| + 2)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.ZetaWide.main
  refine ⟨C₁ + C₂ + 1, by positivity, ?_⟩
  intro N _ χ hprim s hs1 hs2 ht hLs
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog : 1 ≤ Real.log (N * (|s.im| + 2)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  by_cases hχ : χ = 1
  · have hN : N = 1 := by
      have h := hprim
      rw [DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    simp only [LFunction_modOne_eq] at hLs ⊢
    simp only [Nat.cast_one, one_mul] at hlog ⊢
    have hs1' : s ≠ 1 := by
      rintro rfl
      norm_num at ht
    obtain ⟨hfin, hcount, hbound⟩ := h₂ s hs1 hs2 hs1' hLs
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount hbound
    refine ⟨hfin.toFinset, fun w => by simp, ?_, ?_⟩
    · nlinarith
    · have hinv : ‖1 / (s - 1)‖ ≤ 1 / 2 := by
        have h : 2 ≤ ‖s - 1‖ := le_trans ht (by simpa using Complex.abs_im_le_norm (s - 1))
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le (by norm_num) h
      calc ‖deriv riemannZeta s / riemannZeta s
            - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖
          = ‖(deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
            - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)) - 1 / (s - 1)‖ := by
            congr 1; ring
        _ ≤ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
            - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ + ‖1 / (s - 1)‖ :=
            norm_sub_le _ _
        _ ≤ C₂ * Real.log (|s.im| + 2) + 1 / 2 := add_le_add hbound hinv
        _ ≤ (C₁ + C₂ + 1) * Real.log (|s.im| + 2) := by nlinarith
  · obtain ⟨hfin, hcount, hbound⟩ := h₁ N χ hχ s hs1 hs2 hLs
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount hbound
    refine ⟨hfin.toFinset, fun w => ?_, ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => LFunction_apply_one_ne_zero hχ (h ▸ h2), h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    · nlinarith
    · nlinarith

/- English proof (translation)
Take `⟨C, hC, hloc⟩` from `local_formula`. Take `⟨B, hB, hright⟩` from `exists_bound_right`. Use `⟨6 * (3 * C) + 8 * (3 * C) ^ 2 + 4 * B + 1, by positivity, ?_⟩` and prove the remaining obligations. Introduce `N _ χ hprim T hT`. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`.

Establish `hNT : 2 ≤ (N : ℝ) * T` using `by nlinarith`. Use `set L := Real.log (N * T) with hL`. Establish `hLhalf : 1 / 2 ≤ L`. Establish `h1 : Real.log 2 ≤ L` using `Real.log_le_log (by norm_num) hNT`. Establish `h2` using `Real.log_two_gt_d9`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog3 : ∀ y : ℝ, |y| ≤ T + 1 → Real.log (N * (|y| + 2)) ≤ 3 * L`. Introduce `y hy`. Establish `hpos : 0 < (N : ℝ) * (|y| + 2)` using `by positivity`. Establish `h4 : 4 ≤ ((N : ℝ) * T) ^ 2` using `by nlinarith`.

Establish `hle : (N : ℝ) * (|y| + 2) ≤ ((N : ℝ) * T) ^ 3`. Establish `e : ((N : ℝ) * T) ^ 3 = (N * T) * (N * T) ^ 2` using `by ring`. Rewrite using `[e]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ N * T), mul_nonneg (by linarith : (0 : ℝ) ≤ N) (by linarith : (0 : ℝ) ≤ T + 1 - |y|), mul_nonneg (by linarith : (0 : ℝ) ≤ N) (by linarith : (0 : ℝ) ≤ T - 1)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hnorm : ∀ (w : ℂ) (y : ℝ), ‖w - (2 + (y : ℂ) * I)‖ ≤ 7 / 2 ↔ (w.re - 2) ^ 2 + (w.im - y) ^ 2 ≤ 49 / 4`. Introduce `w y`. Establish `e1 : (w - (2 + (y : ℂ) * I)).re = w.re - 2` using `by simp`. Establish `e2 : (w - (2 + (y : ℂ) * I)).im = w.im - y` using `by simp`. Rewrite using `[← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply, e1, e2]`.

Apply the tactic sequence `constructor <;> intro h <;> nlinarith`. Establish `hcover : ∀ (y₀ y : ℝ) (w : ℂ), y₀ ≤ y → y ≤ y₀ + 1 → -1 ≤ w.re → w.re < 1 → ‖w - (2 + (y : ℂ) * I)‖ ≤ 7 / 2 → ‖w - (2 + (y₀ : ℂ) * I)‖ ≤ 7 / 2 ∨ ‖w - (2 + ((y₀ + 1 : ℝ) : ℂ) * I)‖ ≤ 7 / 2`. Introduce `y₀ y w h1 h2 h3 h4 h5`. Rewrite `h5` using `[hnorm]`. Rewrite using `[hnorm, hnorm]`.

Establish `hx : (w.re - 2) ^ 2 ≤ 9` using `by nlinarith`. Distinguish the cases in `hv : w.im ≤ y₀ + 1 / 2`. Use `left`. Distinguish the cases in `hv' : y₀ ≤ w.im`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hv') (sub_nonneg.mpr hv)]`.

Use `push Not at hv'`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ y + y₀ - 2 * w.im)]`. Use `right push Not at hv`. Distinguish the cases in `hv' : w.im ≤ y₀ + 1`. Use polynomial arithmetic with `[mul_nonneg (by linarith : (0 : ℝ) ≤ w.im - y₀ - 1 / 2) (sub_nonneg.mpr hv')]`.

Use `push Not at hv'`. Use polynomial arithmetic with `[mul_nonneg (by linarith : (0 : ℝ) ≤ y₀ + 1 - y) (by linarith : (0 : ℝ) ≤ 2 * w.im - y - y₀ - 1)]`. Establish `hZ : ∀ y : ℝ, 2 ≤ |y| → ∃ Z : Finset ℂ, (∀ w, w ∈ Z ↔ ‖w - (2 + (y : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ LFunction χ w = 0) ∧ (Z.card : ℝ) ≤ C * Real.log (N * (|y| + 2))`. Introduce `y hy`. Establish `hne : (2 : ℂ) + (y : ℂ) * I ≠ 1`.

Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact. Evaluate the numerical expressions using `at this`. Establish `hL2 : LFunction χ (2 + (y : ℂ) * I) ≠ 0` using `LFunction_ne_zero_of_one_le_re χ (.inr hne) (by norm_num)`. Establish `him : (2 + (y : ℂ) * I).im = y` using `by simp`.

Take `⟨Z, hZm, hZc, -⟩` from `hloc N χ hprim (2 + (y : ℂ) * I) (by norm_num) (by norm_num) (by rw [him]; exact hy) hL2`. Rewrite `hZm`, `hZc` using `[him]`. Use `⟨Z, hZm, le_trans ?_ hZc⟩` and prove the remaining obligations. Rewrite using `[Finset.card_eq_sum_ones, Nat.cast_sum]`. Use `Finset.sum_le_sum fun w hw => ?_` and prove the remaining obligations.

Use `one_le_order χ ((hZm w).1 hw).2.1 ((hZm w).1 hw).2.2` as an intermediate fact. Conclude with `this` after adjusting the coercions. Take `⟨Z₁, hZ1m, hZ1c⟩` from `hZ T (by rw [abs_of_pos (by linarith)]; linarith)`. Take `⟨Z₂, hZ2m, hZ2c⟩` from `hZ (T + 1) (by rw [abs_of_pos (by linarith)]; linarith)`. Take `⟨Z₃, hZ3m, hZ3c⟩` from `hZ (-T - 1) (by rw [abs_of_neg (by linarith)]; linarith)`.

Take `⟨Z₄, hZ4m, hZ4c⟩` from `hZ (-T - 1 + 1) (by rw [abs_of_neg (by linarith)]; linarith)`. Establish `hcardle : ∀ (Z : Finset ℂ) (y : ℝ), |y| ≤ T + 1 → (Z.card : ℝ) ≤ C * Real.log (N * (|y| + 2)) → (Z.card : ℝ) ≤ 3 * C * L`. Introduce `Z y hy h`. Use `mul_le_mul_of_nonneg_left (hlog3 y hy) hC.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc1` using `hcardle Z₁ T (by rw [abs_of_pos (by linarith)]; linarith) hZ1c`. Establish `hc2` using `hcardle Z₂ (T + 1) (by rw [abs_of_pos (by linarith)]) hZ2c`. Establish `hc3` using `hcardle Z₃ (-T - 1) (by rw [abs_of_neg (by linarith)]; linarith) hZ3c`. Establish `hc4` using `hcardle Z₄ (-T - 1 + 1) (by rw [abs_of_neg (by linarith)]; linarith) hZ4c`. Use `set S : Finset ℝ := (Z₁ ∪ Z₂).image Complex.im ∪ (Z₃ ∪ Z₄).image (fun w => -w.im) with hS`.

Establish `hScard : S.card ≤ Z₁.card + Z₂.card + (Z₃.card + Z₄.card)`. Combine the equalities or inequalities in the displayed calculation. Establish `hSb : (S.card : ℝ) ≤ 4 * (3 * C * L)`. Establish `: (S.card : ℝ) ≤ Z₁.card + Z₂.card + (Z₃.card + Z₄.card)` using `by exact_mod_cast hScard`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨T', hT1, hT2, hfar⟩` from `exists_far S T`. Use `set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1)) with hδ`. Establish `hδpos : 0 < δ` using `by positivity`. Establish `hδle : δ ≤ 1 / 2`. Rewrite using `[hδ]`.

Apply `one_div_le_one_div_of_le (by norm_num)` to reduce the goal to its premises. Establish `: (0 : ℝ) ≤ S.card` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfar' : ∀ s : ℂ, |s.im| = T' → ∀ w : ℂ, LFunction χ w = 0 → w ≠ 1 → -1 ≤ w.re → ‖w - (2 + (s.im : ℂ) * I)‖ ≤ 7 / 2 → δ ≤ |w.im - s.im|`. Introduce `s hsim w hw0 hw1 hwre hwd`.

Establish `hwre1 : w.re < 1`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `LFunction_ne_zero_of_one_le_re χ (.inr hw1) h hw0`. Break down `(abs_eq (by linarith : (0 : ℝ) ≤ T')).mp hsim with h | h` into its components or cases.

Rewrite `hwd`, the goal using `[h]`. Break down `hcover T T' w hT1 hT2 hwre hwre1 hwd with h' | h'` into its components or cases. Establish `hm : w.im ∈ S` using `Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ ((hZ1m w).2 ⟨h', hw1, hw0⟩), rfl⟩)`. Conclude with `hfar _ hm`. Establish `hm : w.im ∈ S` using `Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ ((hZ2m w).2 ⟨h', hw1, hw0⟩), rfl⟩)`.

Conclude with `hfar _ hm`. Rewrite `hwd`, the goal using `[h]`. Establish `hdist : |-w.im - T'| = |w.im - -T'|`. Rewrite using `[← abs_neg]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Break down `hcover (-T - 1) (-T') w (by linarith) (by linarith) hwre hwre1 hwd with h' | h'` into its components or cases. Establish `hm : -w.im ∈ S` using `Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ ((hZ3m w).2 ⟨h', hw1, hw0⟩), rfl⟩)`. Rewrite using `[← hdist]`. Conclude with `hfar _ hm`.

Establish `hm : -w.im ∈ S` using `Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ ((hZ4m w).2 ⟨h', hw1, hw0⟩), rfl⟩)`. Rewrite using `[← hdist]`. Conclude with `hfar _ hm`. Use `clear_value δ S L`. Use `⟨T', hT1, hT2, ?_⟩` and prove the remaining obligations.

Introduce `s hs1 hs2 hsim`. Establish `hT'pos : 0 < T'` using `by linarith`. Establish `hLs : LFunction χ s ≠ 0`. Introduce `h0`. Establish `hs1' : s ≠ 1`.

Introduce and unpack `rfl`. Simplify using `at hsim`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : ‖s - (2 + (s.im : ℂ) * I)‖ ≤ 7 / 2`. Rewrite using `[hnorm]`.

Use the polynomial consequences of the given equalities and inequalities. Use `hfar' s hsim s h0 hs1' (by linarith) hd` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hLs, ?_⟩` and prove the remaining obligations.

Establish `hL0 : 0 ≤ L` using `by linarith`. Establish `hKL : 0 ≤ 3 * C * L` using `by positivity`. Distinguish the cases in `hre : 2 ≤ s.re`. Establish `h` using `hright N χ s hre`. Establish `h4L : 0 ≤ 4 * L ^ 2 - 1` using `by nlinarith`.

Establish `e1 : 0 ≤ B * (4 * L ^ 2 - 1)` using `mul_nonneg hB h4L`. Establish `e2 : 0 ≤ C * L ^ 2` using `mul_nonneg hC.le (sq_nonneg L)`. Establish `e3 : 0 ≤ C ^ 2 * L ^ 2` using `mul_nonneg (sq_nonneg C) (sq_nonneg L)`. Establish `e4 : 0 ≤ L ^ 2` using `sq_nonneg L`. Use the polynomial consequences of the given equalities and inequalities.

Use `push Not at hre`. Take `⟨Z, hZm, hZc, hdiff⟩` from `hloc N χ hprim s (by linarith) hre.le (by rw [hsim]; linarith) hLs`. Establish `hlogs : Real.log (N * (|s.im| + 2)) ≤ 3 * L` using `hlog3 _ (by rw [hsim]; linarith)`. Establish `hsep : ∀ w ∈ Z, δ ≤ ‖s - w‖`. Introduce `w hw`.

Take `⟨hwd, hw1, hw0⟩` from `(hZm w).1 hw`. Distinguish the cases in `hwre : -1 ≤ w.re`. Combine the equalities or inequalities in the displayed calculation. Use `push Not at hwre`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsumle : ‖∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ (∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℝ)) * (2 * ((S.card : ℝ) + 1))`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `w hw`. Rewrite using `[norm_div, Complex.norm_natCast]`.

Conclude with `div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδpos (hsep w hw)`. Use `_ = _ := by rw [← Finset.sum_div, hδ, div_div_eq_mul_div, div_one]`. Establish `hordsum : (∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℝ)) ≤ 3 * C * L`. Use `mul_le_mul_of_nonneg_left hlogs hC.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hD : ‖deriv (LFunction χ) s / LFunction χ s - ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ 3 * C * L`. Use `mul_le_mul_of_nonneg_left hlogs hC.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum2 : ‖∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ 3 * C * L * (2 * (4 * (3 * C * L) + 1))`. Establish `hb : 2 * ((S.card : ℝ) + 1) ≤ 2 * (4 * (3 * C * L) + 1)` using `by linarith only [hSb]`.

Establish `hb0 : (0 : ℝ) ≤ 2 * ((S.card : ℝ) + 1)`. Establish `: (0 : ℝ) ≤ S.card` using `Nat.cast_nonneg _`. Combine the linear relations using `only [this]`. Conclude with `le_trans hsumle (mul_le_mul hordsum hb hb0 hKL)`. Establish `htri : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ ‖deriv (LFunction χ) s / LFunction χ s - ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ + ‖∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖`.

Combine the equalities or inequalities in the displayed calculation. Establish `g1 : 0 ≤ C * (L * (2 * L - 1))` using `mul_nonneg hC.le (mul_nonneg hL0 (by linarith only [hLhalf]))`. Establish `g2 : 0 ≤ B * L ^ 2` using `mul_nonneg hB (sq_nonneg L)`. Establish `g3 : 0 ≤ L ^ 2` using `sq_nonneg L`. Use polynomial arithmetic with `only [htri, hD, hsum2, g1, g2, g3]`.
-/
theorem exists_height : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T → ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ ∀ s : ℂ, -(1/2 : ℝ) ≤ s.re → s.re ≤ 3 → |s.im| = T' → LFunction χ s ≠ 0 ∧ ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ C * Real.log (N * T) ^ 2 := by
  obtain ⟨C, hC, hloc⟩ := local_formula
  obtain ⟨B, hB, hright⟩ := exists_bound_right
  refine ⟨6 * (3 * C) + 8 * (3 * C) ^ 2 + 4 * B + 1, by positivity, ?_⟩
  intro N _ χ hprim T hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNT : 2 ≤ (N : ℝ) * T := by nlinarith
  set L := Real.log (N * T) with hL
  have hLhalf : 1 / 2 ≤ L := by
    have h1 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hNT
    have h2 := Real.log_two_gt_d9
    linarith
  have hlog3 : ∀ y : ℝ, |y| ≤ T + 1 → Real.log (N * (|y| + 2)) ≤ 3 * L := by
    intro y hy
    have hpos : 0 < (N : ℝ) * (|y| + 2) := by positivity
    have h4 : 4 ≤ ((N : ℝ) * T) ^ 2 := by nlinarith
    have hle : (N : ℝ) * (|y| + 2) ≤ ((N : ℝ) * T) ^ 3 := by
      have e : ((N : ℝ) * T) ^ 3 = (N * T) * (N * T) ^ 2 := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ N * T),
        mul_nonneg (by linarith : (0 : ℝ) ≤ N) (by linarith : (0 : ℝ) ≤ T + 1 - |y|),
        mul_nonneg (by linarith : (0 : ℝ) ≤ N) (by linarith : (0 : ℝ) ≤ T - 1)]
    calc Real.log (N * (|y| + 2)) ≤ Real.log (((N : ℝ) * T) ^ 3) := Real.log_le_log hpos hle
      _ = 3 * L := by rw [Real.log_pow]; push_cast; ring
  have hnorm : ∀ (w : ℂ) (y : ℝ),
      ‖w - (2 + (y : ℂ) * I)‖ ≤ 7 / 2 ↔ (w.re - 2) ^ 2 + (w.im - y) ^ 2 ≤ 49 / 4 := by
    intro w y
    have e1 : (w - (2 + (y : ℂ) * I)).re = w.re - 2 := by simp
    have e2 : (w - (2 + (y : ℂ) * I)).im = w.im - y := by simp
    rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply, e1, e2]
    constructor <;> intro h <;> nlinarith
  have hcover : ∀ (y₀ y : ℝ) (w : ℂ), y₀ ≤ y → y ≤ y₀ + 1 → -1 ≤ w.re → w.re < 1 →
      ‖w - (2 + (y : ℂ) * I)‖ ≤ 7 / 2 →
      ‖w - (2 + (y₀ : ℂ) * I)‖ ≤ 7 / 2 ∨ ‖w - (2 + ((y₀ + 1 : ℝ) : ℂ) * I)‖ ≤ 7 / 2 := by
    intro y₀ y w h1 h2 h3 h4 h5
    rw [hnorm] at h5
    rw [hnorm, hnorm]
    have hx : (w.re - 2) ^ 2 ≤ 9 := by nlinarith
    by_cases hv : w.im ≤ y₀ + 1 / 2
    · left
      by_cases hv' : y₀ ≤ w.im
      · nlinarith [mul_nonneg (sub_nonneg.mpr hv') (sub_nonneg.mpr hv)]
      · push Not at hv'
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ y + y₀ - 2 * w.im)]
    · right
      push Not at hv
      by_cases hv' : w.im ≤ y₀ + 1
      · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ w.im - y₀ - 1 / 2) (sub_nonneg.mpr hv')]
      · push Not at hv'
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y₀ + 1 - y)
          (by linarith : (0 : ℝ) ≤ 2 * w.im - y - y₀ - 1)]
  have hZ : ∀ y : ℝ, 2 ≤ |y| → ∃ Z : Finset ℂ,
      (∀ w, w ∈ Z ↔ ‖w - (2 + (y : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ LFunction χ w = 0) ∧
      (Z.card : ℝ) ≤ C * Real.log (N * (|y| + 2)) := by
    intro y hy
    have hne : (2 : ℂ) + (y : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    have hL2 : LFunction χ (2 + (y : ℂ) * I) ≠ 0 :=
      LFunction_ne_zero_of_one_le_re χ (.inr hne) (by norm_num)
    have him : (2 + (y : ℂ) * I).im = y := by simp
    obtain ⟨Z, hZm, hZc, -⟩ := hloc N χ hprim (2 + (y : ℂ) * I) (by norm_num) (by norm_num)
      (by rw [him]; exact hy) hL2
    rw [him] at hZm hZc
    refine ⟨Z, hZm, le_trans ?_ hZc⟩
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    have := one_le_order χ ((hZm w).1 hw).2.1 ((hZm w).1 hw).2.2
    exact_mod_cast this
  obtain ⟨Z₁, hZ1m, hZ1c⟩ := hZ T (by rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨Z₂, hZ2m, hZ2c⟩ := hZ (T + 1) (by rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨Z₃, hZ3m, hZ3c⟩ := hZ (-T - 1) (by rw [abs_of_neg (by linarith)]; linarith)
  obtain ⟨Z₄, hZ4m, hZ4c⟩ := hZ (-T - 1 + 1) (by rw [abs_of_neg (by linarith)]; linarith)
  have hcardle : ∀ (Z : Finset ℂ) (y : ℝ), |y| ≤ T + 1 →
      (Z.card : ℝ) ≤ C * Real.log (N * (|y| + 2)) → (Z.card : ℝ) ≤ 3 * C * L := by
    intro Z y hy h
    have := mul_le_mul_of_nonneg_left (hlog3 y hy) hC.le
    linarith
  have hc1 := hcardle Z₁ T (by rw [abs_of_pos (by linarith)]; linarith) hZ1c
  have hc2 := hcardle Z₂ (T + 1) (by rw [abs_of_pos (by linarith)]) hZ2c
  have hc3 := hcardle Z₃ (-T - 1) (by rw [abs_of_neg (by linarith)]; linarith) hZ3c
  have hc4 := hcardle Z₄ (-T - 1 + 1) (by rw [abs_of_neg (by linarith)]; linarith) hZ4c
  set S : Finset ℝ := (Z₁ ∪ Z₂).image Complex.im ∪ (Z₃ ∪ Z₄).image (fun w => -w.im) with hS
  have hScard : S.card ≤ Z₁.card + Z₂.card + (Z₃.card + Z₄.card) := by
    calc S.card ≤ ((Z₁ ∪ Z₂).image Complex.im).card + ((Z₃ ∪ Z₄).image fun w => -w.im).card :=
          Finset.card_union_le _ _
      _ ≤ (Z₁ ∪ Z₂).card + (Z₃ ∪ Z₄).card := add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ _ := add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)
  have hSb : (S.card : ℝ) ≤ 4 * (3 * C * L) := by
    have : (S.card : ℝ) ≤ Z₁.card + Z₂.card + (Z₃.card + Z₄.card) := by exact_mod_cast hScard
    linarith
  obtain ⟨T', hT1, hT2, hfar⟩ := exists_far S T
  set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 2 := by
    rw [hδ]
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    linarith
  have hfar' : ∀ s : ℂ, |s.im| = T' → ∀ w : ℂ, LFunction χ w = 0 → w ≠ 1 → -1 ≤ w.re →
      ‖w - (2 + (s.im : ℂ) * I)‖ ≤ 7 / 2 → δ ≤ |w.im - s.im| := by
    intro s hsim w hw0 hw1 hwre hwd
    have hwre1 : w.re < 1 := by
      by_contra h
      push Not at h
      exact LFunction_ne_zero_of_one_le_re χ (.inr hw1) h hw0
    rcases (abs_eq (by linarith : (0 : ℝ) ≤ T')).mp hsim with h | h
    · rw [h] at hwd ⊢
      rcases hcover T T' w hT1 hT2 hwre hwre1 hwd with h' | h'
      · have hm : w.im ∈ S := Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ ((hZ1m w).2 ⟨h', hw1, hw0⟩), rfl⟩)
        exact hfar _ hm
      · have hm : w.im ∈ S := Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ ((hZ2m w).2 ⟨h', hw1, hw0⟩), rfl⟩)
        exact hfar _ hm
    · rw [h] at hwd ⊢
      have hdist : |-w.im - T'| = |w.im - -T'| := by
        rw [← abs_neg]; congr 1; ring
      rcases hcover (-T - 1) (-T') w (by linarith) (by linarith) hwre hwre1 hwd with h' | h'
      · have hm : -w.im ∈ S := Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ ((hZ3m w).2 ⟨h', hw1, hw0⟩), rfl⟩)
        rw [← hdist]
        exact hfar _ hm
      · have hm : -w.im ∈ S := Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ ((hZ4m w).2 ⟨h', hw1, hw0⟩), rfl⟩)
        rw [← hdist]
        exact hfar _ hm
  clear_value δ S L
  refine ⟨T', hT1, hT2, ?_⟩
  intro s hs1 hs2 hsim
  have hT'pos : 0 < T' := by linarith
  have hLs : LFunction χ s ≠ 0 := by
    intro h0
    have hs1' : s ≠ 1 := by
      rintro rfl
      simp at hsim
      linarith
    have hd : ‖s - (2 + (s.im : ℂ) * I)‖ ≤ 7 / 2 := by
      rw [hnorm]
      nlinarith
    have := hfar' s hsim s h0 hs1' (by linarith) hd
    simp at this
    linarith
  refine ⟨hLs, ?_⟩
  have hL0 : 0 ≤ L := by linarith
  have hKL : 0 ≤ 3 * C * L := by positivity
  by_cases hre : 2 ≤ s.re
  · have h := hright N χ s hre
    have h4L : 0 ≤ 4 * L ^ 2 - 1 := by nlinarith
    have e1 : 0 ≤ B * (4 * L ^ 2 - 1) := mul_nonneg hB h4L
    have e2 : 0 ≤ C * L ^ 2 := mul_nonneg hC.le (sq_nonneg L)
    have e3 : 0 ≤ C ^ 2 * L ^ 2 := mul_nonneg (sq_nonneg C) (sq_nonneg L)
    have e4 : 0 ≤ L ^ 2 := sq_nonneg L
    nlinarith
  · push Not at hre
    obtain ⟨Z, hZm, hZc, hdiff⟩ := hloc N χ hprim s (by linarith) hre.le (by rw [hsim]; linarith) hLs
    have hlogs : Real.log (N * (|s.im| + 2)) ≤ 3 * L := hlog3 _ (by rw [hsim]; linarith)
    have hsep : ∀ w ∈ Z, δ ≤ ‖s - w‖ := by
      intro w hw
      obtain ⟨hwd, hw1, hw0⟩ := (hZm w).1 hw
      by_cases hwre : -1 ≤ w.re
      · calc δ ≤ |w.im - s.im| := hfar' s hsim w hw0 hw1 hwre hwd
          _ = |(s - w).im| := by rw [Complex.sub_im, abs_sub_comm]
          _ ≤ ‖s - w‖ := Complex.abs_im_le_norm _
      · push Not at hwre
        calc δ ≤ 1 / 2 := hδle
          _ ≤ |(s - w).re| := by rw [Complex.sub_re, abs_of_pos (by linarith)]; linarith
          _ ≤ ‖s - w‖ := Complex.abs_re_le_norm _
    have hsumle : ‖∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖
        ≤ (∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℝ)) * (2 * ((S.card : ℝ) + 1)) := by
      calc ‖∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖
          ≤ ∑ w ∈ Z, ‖(analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ := norm_sum_le _ _
        _ ≤ ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℝ) / δ := by
          apply Finset.sum_le_sum
          intro w hw
          rw [norm_div, Complex.norm_natCast]
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδpos (hsep w hw)
        _ = _ := by rw [← Finset.sum_div, hδ, div_div_eq_mul_div, div_one]
    have hordsum : (∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℝ)) ≤ 3 * C * L := by
      have := mul_le_mul_of_nonneg_left hlogs hC.le
      linarith
    have hD : ‖deriv (LFunction χ) s / LFunction χ s
        - ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ 3 * C * L := by
      have := mul_le_mul_of_nonneg_left hlogs hC.le
      linarith
    have hsum2 : ‖∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖
        ≤ 3 * C * L * (2 * (4 * (3 * C * L) + 1)) :=
      by
        have hb : 2 * ((S.card : ℝ) + 1) ≤ 2 * (4 * (3 * C * L) + 1) := by linarith only [hSb]
        have hb0 : (0 : ℝ) ≤ 2 * ((S.card : ℝ) + 1) := by
          have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
          linarith only [this]
        exact le_trans hsumle (mul_le_mul hordsum hb hb0 hKL)
    have htri : ‖deriv (LFunction χ) s / LFunction χ s‖
        ≤ ‖deriv (LFunction χ) s / LFunction χ s
            - ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖
          + ‖∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ := by
      calc ‖deriv (LFunction χ) s / LFunction χ s‖
          = ‖(deriv (LFunction χ) s / LFunction χ s
            - ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w))
            + ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have g1 : 0 ≤ C * (L * (2 * L - 1)) :=
      mul_nonneg hC.le (mul_nonneg hL0 (by linarith only [hLhalf]))
    have g2 : 0 ≤ B * L ^ 2 := mul_nonneg hB (sq_nonneg L)
    have g3 : 0 ≤ L ^ 2 := sq_nonneg L
    nlinarith only [htri, hD, hsum2, g1, g2, g3]

end GlobalTheory.GoodHeight
