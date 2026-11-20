import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.HalfLeNormLentCtr

noncomputable section

namespace PI.EF

open Complex Metric Filter Topology Set DirichletCharacter

variable {N : ℕ} [NeZero N]

def DZ (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ := {ρ | ρ ∈ closedBall (ctr t) (11 / 4) ∧ Lent χ ρ = 0}

/- English proof (translation)
Rewrite using `[← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ctr_re, ctr_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_sub_ctr_sq (ρ : ℂ) (t : ℝ) : ‖ρ - ctr t‖ ^ 2 = (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ctr_re, ctr_im]
  ring

/- English proof (translation)
Unfold `Lent`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hρ, sub_eq_zero]`. Conclude with `Iff.rfl`.
-/
private lemma Lent_eq_zero_iff_LFunction_eq_zero_of_ne_one (χ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ : ρ ≠ 1) :
    Lent χ ρ = 0 ↔ LFunction χ ρ = 0 := by
  unfold Lent
  split_ifs with h
  · subst h
    simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hρ, sub_eq_zero]
  · exact Iff.rfl

/- English proof (translation)
Take `⟨hb, hz⟩` from `hρ`. Rewrite `hb` using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `hsq` using `norm_sub_ctr_sq ρ t`. Establish `hn` using `norm_nonneg (ρ - ctr t)`. Establish `hx2 : ‖ρ - ctr t‖ ^ 2 ≤ (11 / 4) ^ 2` using `by nlinarith`.

Establish `hre : -3 / 4 ≤ ρ.re` using `by nlinarith [sq_nonneg (ρ.im - t)]`. Establish `him : |ρ.im - t| ≤ 3`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> nlinarith [sq_nonneg (ρ.re - 2)]`. Establish `hne : ρ ≠ 1`.

Introduce and unpack `rfl`. Unfold `Lent at hz`. Use `split_ifs at hz with h`. Substitute `h first` using the available equality. Consider the case `exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero _ hz`.

Consider the case `exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero hz`. Conclude with `DirichletCharacter.LFunction_apply_one_ne_zero h hz`. Establish `hL : LFunction χ ρ = 0` using `(Lent_eq_zero_iff_LFunction_eq_zero_of_ne_one χ hne).1 hz`. Use `⟨hne, hL, him, ?_⟩` and prove the remaining obligations. Break down `hZL N χ hχ ρ (by linarith) hne hL with h | h | ⟨rfl, -⟩` into its components or cases.

Conclude with `Or.inl h`. Conclude with `Or.inr h`. Evaluate the numerical expressions using `at hre`.
-/
lemma DZ_facts (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ DZ χ t) :
    ρ ≠ 1 ∧ LFunction χ ρ = 0 ∧ |ρ.im - t| ≤ 3 ∧
      ((0 < ρ.re ∧ ρ.re < 1) ∨ (ρ = 0 ∧ χ.Even ∧ χ ≠ 1)) := by
  obtain ⟨hb, hz⟩ := hρ
  rw [Metric.mem_closedBall, dist_eq_norm] at hb
  have hsq := norm_sub_ctr_sq ρ t
  have hn := norm_nonneg (ρ - ctr t)
  have hx2 : ‖ρ - ctr t‖ ^ 2 ≤ (11 / 4) ^ 2 := by nlinarith
  have hre : -3 / 4 ≤ ρ.re := by nlinarith [sq_nonneg (ρ.im - t)]
  have him : |ρ.im - t| ≤ 3 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (ρ.re - 2)]
  have hne : ρ ≠ 1 := by
    rintro rfl
    unfold Lent at hz
    split_ifs at hz with h
    · subst h
      first
        | exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero _ hz
        | exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero hz
    · exact DirichletCharacter.LFunction_apply_one_ne_zero h hz
  have hL : LFunction χ ρ = 0 := (Lent_eq_zero_iff_LFunction_eq_zero_of_ne_one χ hne).1 hz
  refine ⟨hne, hL, him, ?_⟩
  rcases hZL N χ hχ ρ (by linarith) hne hL with h | h | ⟨rfl, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · norm_num at hre

/- English proof (translation)
Establish `hE' : ∀ ρ ∈ E, 1 ≤ ‖s - ρ‖ ∧ (ρ ∈ ZerosNear χ (t + 2) ∨ ρ ∈ ZerosNear χ (t - 2))`. Introduce `ρ hρ`. Take `⟨hD, hN, h0⟩` from `hE ρ hρ`. Take `⟨-, hL, him, hcase⟩` from `DZ_facts hZL hχ hD`. Establish `hstrip : 0 < ρ.re ∧ ρ.re < 1`.

Break down `hcase with h | ⟨h, -⟩` into its components or cases. Conclude with `h`. Conclude with `absurd h h0`. Establish `hfar : 1 < |ρ.im - t|`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hN ⟨hstrip.1, hstrip.2, hc, hL⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Break down `le_or_gt 0 (ρ.im - t) with h | h` into its components or cases.

Use `left`. Use `⟨hstrip.1, hstrip.2, ?_, hL⟩` and prove the remaining obligations. Rewrite `hfar`, `him` using `[abs_of_nonneg h]`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.

Use `right`. Use `⟨hstrip.1, hstrip.2, ?_, hL⟩` and prove the remaining obligations. Rewrite `hfar`, `him` using `[abs_of_neg h]`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.

Take `⟨hfinP, hsumP⟩` from `hW N χ hχ (t + 2)`. Take `⟨hfinM, hsumM⟩` from `hW N χ hχ (t - 2)`. Establish `step1 : ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ E, (mult χ ρ : ℝ)`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)` and prove the remaining obligations. Rewrite using `[norm_div]`.

Establish `h1` using `(hE' ρ hρ).1`. Establish `hc : ‖(mult χ ρ : ℂ)‖ = (mult χ ρ : ℝ)` using `by first`. Consider the case `exact Complex.norm_natCast _`. Consider the case `simp`. Rewrite using `[hc]`.

Conclude with `div_le_self (Nat.cast_nonneg _) h1`. Establish `step2 : ∑ ρ ∈ E, (mult χ ρ : ℝ) ≤ ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) + ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ)`. Establish `hsub : E ⊆ hfinP.toFinset ∪ hfinM.toFinset`. Introduce `ρ hρ`. Rewrite using `[Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]`.

Conclude with `(hE' ρ hρ).2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_union_inter]`. Conclude with `le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)`. Establish `hP : ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t + 2| + 2))`.

Combine the equalities or inequalities in the displayed calculation. Establish `hM : ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t - 2| + 2))`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma far_sum_le {Cw : ℝ} (hW : ZerosWindowWith Cw) (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {t : ℝ} (s : ℂ) (hs : s.im = t) (E : Finset ℂ)
    (hE : ∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) :
    ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      Cw * Real.log (N * (|t + 2| + 2)) + Cw * Real.log (N * (|t - 2| + 2)) := by
  classical
  have hE' : ∀ ρ ∈ E, 1 ≤ ‖s - ρ‖ ∧ (ρ ∈ ZerosNear χ (t + 2) ∨ ρ ∈ ZerosNear χ (t - 2)) := by
    intro ρ hρ
    obtain ⟨hD, hN, h0⟩ := hE ρ hρ
    obtain ⟨-, hL, him, hcase⟩ := DZ_facts hZL hχ hD
    have hstrip : 0 < ρ.re ∧ ρ.re < 1 := by
      rcases hcase with h | ⟨h, -⟩
      · exact h
      · exact absurd h h0
    have hfar : 1 < |ρ.im - t| := by
      by_contra hc
      push_neg at hc
      exact hN ⟨hstrip.1, hstrip.2, hc, hL⟩
    refine ⟨?_, ?_⟩
    · calc (1 : ℝ) ≤ |ρ.im - t| := hfar.le
        _ = |(s - ρ).im| := by rw [Complex.sub_im, hs, abs_sub_comm]
        _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
    · rcases le_or_gt 0 (ρ.im - t) with h | h
      · left
        refine ⟨hstrip.1, hstrip.2, ?_, hL⟩
        rw [abs_of_nonneg h] at hfar him
        rw [abs_le]
        constructor <;> linarith
      · right
        refine ⟨hstrip.1, hstrip.2, ?_, hL⟩
        rw [abs_of_neg h] at hfar him
        rw [abs_le]
        constructor <;> linarith
  obtain ⟨hfinP, hsumP⟩ := hW N χ hχ (t + 2)
  obtain ⟨hfinM, hsumM⟩ := hW N χ hχ (t - 2)
  have step1 : ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ E, (mult χ ρ : ℝ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    rw [norm_div]
    have h1 := (hE' ρ hρ).1
    have hc : ‖(mult χ ρ : ℂ)‖ = (mult χ ρ : ℝ) := by
      first
        | exact Complex.norm_natCast _
        | simp
    rw [hc]
    exact div_le_self (Nat.cast_nonneg _) h1
  have step2 : ∑ ρ ∈ E, (mult χ ρ : ℝ) ≤
      ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) + ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) := by
    have hsub : E ⊆ hfinP.toFinset ∪ hfinM.toFinset := by
      intro ρ hρ
      rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact (hE' ρ hρ).2
    calc ∑ ρ ∈ E, (mult χ ρ : ℝ) ≤ ∑ ρ ∈ hfinP.toFinset ∪ hfinM.toFinset, (mult χ ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) + ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) := by
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hP : ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t + 2| + 2)) := by
    calc _ = ∑ᶠ ρ ∈ ZerosNear χ (t + 2), (mult χ ρ : ℝ) :=
          (finsum_mem_eq_finite_toFinset_sum _ hfinP).symm
      _ ≤ _ := hsumP
  have hM : ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t - 2| + 2)) := by
    calc _ = ∑ᶠ ρ ∈ ZerosNear χ (t - 2), (mult χ ρ : ℝ) :=
          (finsum_mem_eq_finite_toFinset_sum _ hfinM).symm
      _ ≤ _ := hsumM
  linarith

/- English proof (translation)
Distinguish the cases in `h0 : (0 : ℂ) ∈ DZ χ t`. Take `⟨-, hL, -, h⟩` from `DZ_facts hZL hχ h0`. Break down `h with h | h` into its components or cases. Simplify using `at h`. Take `⟨-, he, h1⟩` from `h`.

Establish `hm` using `(mult_zero_of_even hχ he h1).2`. Simplify using `only [h0, if_true, mult, hm, eps0, he, h1, ne_eq, not_false_eq_true, and_self, sub_zero]`. Simplify using the standard rewrite rules. Simplify using `only [h0, if_false, zero_sub, norm_neg]`. Unfold `eps0`.

Use `split_ifs with he`. Establish `hL` using `(mult_zero_of_even hχ he.1 he.2).1`. Establish `h0' : ¬ ((0 : ℂ) ∈ closedBall (ctr t) (11 / 4))`. Introduce `hb`. Conclude with `h0 ⟨hb, (Lent_eq_zero_iff χ (by norm_num)).2 hL⟩`.

Rewrite `h0'` using `[mem_closedBall, dist_eq_norm, not_le, zero_sub]`. Establish `h1` using `norm_sub_ctr_sq 0 t`. Simplify using `only [zero_re, zero_im, zero_sub] at h1`. Establish `h2 : 1 < t ^ 2` using `by nlinarith [norm_nonneg (-ctr t)]`. Establish `h3 : 1 ≤ ‖s‖`.

Establish `h4` using `Complex.abs_im_le_norm s`. Rewrite `h4` using `[hs]`. Establish `h5 : 1 < |t|`. Assume the negation of the conclusion as `h6`. Use `abs_le.1 (not_lt.1 h6)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[norm_div, norm_one]`. Conclude with `div_le_one_of_le₀ h3 (norm_nonneg _)`. Simplify using the standard rewrite rules.
-/
lemma zero_term_le (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ}
    (s : ℂ) (hs : s.im = t) :
    ‖(open Classical in if (0 : ℂ) ∈ DZ χ t then (mult χ 0 : ℂ) / (s - 0) else 0) - eps0 χ / s‖
      ≤ 1 := by
  classical
  by_cases h0 : (0 : ℂ) ∈ DZ χ t
  · obtain ⟨-, hL, -, h⟩ := DZ_facts hZL hχ h0
    rcases h with h | h
    · simp at h
    · obtain ⟨-, he, h1⟩ := h
      have hm := (mult_zero_of_even hχ he h1).2
      simp only [h0, if_true, mult, hm, eps0, he, h1, ne_eq, not_false_eq_true, and_self, sub_zero]
      simp
  · simp only [h0, if_false, zero_sub, norm_neg]
    unfold eps0
    split_ifs with he
    · have hL := (mult_zero_of_even hχ he.1 he.2).1
      have h0' : ¬ ((0 : ℂ) ∈ closedBall (ctr t) (11 / 4)) := by
        intro hb
        exact h0 ⟨hb, (Lent_eq_zero_iff χ (by norm_num)).2 hL⟩
      rw [mem_closedBall, dist_eq_norm, not_le, zero_sub] at h0'
      have h1 := norm_sub_ctr_sq 0 t
      simp only [zero_re, zero_im, zero_sub] at h1
      have h2 : 1 < t ^ 2 := by nlinarith [norm_nonneg (-ctr t)]
      have h3 : 1 ≤ ‖s‖ := by
        have h4 := Complex.abs_im_le_norm s
        rw [hs] at h4
        have h5 : 1 < |t| := by
          by_contra h6
          have := abs_le.1 (not_lt.1 h6)
          nlinarith
        linarith
      rw [norm_div, norm_one]
      exact div_le_one_of_le₀ h3 (norm_nonneg _)
    · simp

end PI.EF
