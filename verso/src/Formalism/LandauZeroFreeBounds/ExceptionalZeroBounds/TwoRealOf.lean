import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hre : ρ.re < 1`. Assume the negation of the conclusion as `h`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h) hρ`. Establish `hw : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re = σ - ρ.re` using `by simp`. Establish `hwpos : 0 < ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re` using `by rw [hw]; linarith`.

Rewrite using `[one_div, Complex.inv_re]`. Apply `div_pos hwpos` to reduce the goal to its premises. Rewrite using `[Complex.normSq_pos]`. Introduce `h0`. Rewrite `hwpos` using `[h0]`.

Simplify using `at hwpos`.
-/
lemma re_one_div_sub_zero_pos_bis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h) hρ
  have hw : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re = σ - ρ.re := by simp
  have hwpos : 0 < ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re := by rw [hw]; linarith
  rw [one_div, Complex.inv_re]
  apply div_pos hwpos
  rw [Complex.normSq_pos]
  intro h0
  rw [h0] at hwpos
  simp at hwpos

/- English proof (translation)
Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `ρ hρ`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ (hZ ρ hρ) σ hσ).le`.
-/
lemma sum_re_one_div_sub_zero_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : Finset ℂ)
    (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
  apply Finset.sum_nonneg
  intro ρ hρ
  exact mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ (hZ ρ hρ) σ hσ).le

/- English proof (translation)
Establish `hs0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = (σ : ℂ)` using `by simp`. Establish `hl : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re = (negLD χ (σ : ℂ)).re`. Rewrite using `[hs0]`. Establish `h02 : |(0 : ℝ)| + 2 = 2` using `by norm_num`. Rewrite `hb` using `[h02]`.

Establish `hβZ : (β : ℂ) ∈ Z`. Rewrite using `[hZ]`. Use `⟨?_, hzero⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `h' : (β : ℂ) - ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((β - 11 / 10 : ℝ) : ℂ)` using `by push_cast; ring`.

Rewrite using `[h', Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `hterm : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re = 1 / (σ - β)`. Establish `h' : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))) = ((1 / (σ - β) : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[h', Complex.ofReal_re]`.

Establish `hrest : 0 ≤ ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re`. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `ρ hρ`. Establish `hρZ` using `((hZ ρ).1 (Finset.mem_of_mem_erase hρ)).2`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ hρZ σ hσ).le`.

Establish `hsplit : (m (β : ℂ) : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re + ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re = ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re` using `Finset.add_sum_erase Z (fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) hβZ`. Rewrite `hsplit` using `[hterm]`. Establish `hpos : 0 < 1 / (σ - β)` using `one_div_pos.mpr (sub_pos.mpr hβσ)`. Establish `hm : (1 : ℝ) ≤ (m (β : ℂ) : ℝ)` using `by exact_mod_cast hm1 _ hβZ`. Establish `hbig : 1 / (σ - β) ≤ (m (β : ℂ) : ℝ) * (1 / (σ - β))` using `by nlinarith`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma re_negLogDeriv_le_of_real_zero (C : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔
        (ρ ∈ Metric.closedBall ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) (1 / 5) ∧
          DirichletCharacter.LFunction χ ρ = 0))
    (hm1 : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (β σ : ℝ) (hσ : 1 < σ) (hβσ : β < σ) (hβ9 : 9 / 10 ≤ β) (hβ1 : β < 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hb : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re ≤
      C * Real.log ((q : ℝ) * (|(0 : ℝ)| + 2)) -
        ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) :
    (negLD χ (σ : ℂ)).re ≤ C * Real.log ((q : ℝ) * 2) - 1 / (σ - β) := by
  have hs0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = (σ : ℂ) := by simp
  have hl : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re = (negLD χ (σ : ℂ)).re := by
    rw [hs0]
  have h02 : |(0 : ℝ)| + 2 = 2 := by norm_num
  rw [h02] at hb
  have hβZ : (β : ℂ) ∈ Z := by
    rw [hZ]
    refine ⟨?_, hzero⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h' : (β : ℂ) - ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((β - 11 / 10 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h', Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hterm : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re = 1 / (σ - β) := by
    have h' : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))) = ((1 / (σ - β) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h', Complex.ofReal_re]
  have hrest : 0 ≤ ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρZ := ((hZ ρ).1 (Finset.mem_of_mem_erase hρ)).2
    exact mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ hρZ σ hσ).le
  have hsplit : (m (β : ℂ) : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re +
      ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re =
      ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re :=
    Finset.add_sum_erase Z (fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) hβZ
  rw [hterm] at hsplit
  have hpos : 0 < 1 / (σ - β) := one_div_pos.mpr (sub_pos.mpr hβσ)
  have hm : (1 : ℝ) ≤ (m (β : ℂ) : ℝ) := by exact_mod_cast hm1 _ hβZ
  have hbig : 1 / (σ - β) ≤ (m (β : ℂ) : ℝ) * (1 / (σ - β)) := by nlinarith
  linarith

/- English proof (translation)
Introduce `hZS hLD hPos`. Take `⟨C, hC⟩` from `hZS`. Take `⟨C', hC'0, hC'⟩` from `hLD`. Take `⟨A, hA⟩ : ∃ A : ℝ, A = 3 * |C| + 2 * C' + 1` from `⟨_, rfl⟩`. Establish `hA1 : 1 ≤ A` using `by have := abs_nonneg C; linarith`.

Establish `hA0 : 0 < A` using `by linarith`. Use `⟨1 / (20 * A), one_div_pos.mpr (mul_pos (by norm_num) hA0), ?_⟩` and prove the remaining obligations. Introduce `q hq0 χ₁ χ₂ h₁ h₂ h₁1 h₂1 h12 β₁ β₂ hr₁ hr₂`. Assume the negation of the conclusion as `hcon`. Take `⟨hz₁', hz₂'⟩` from `not_or.mp hcon`.

Establish `hz₁` using `not_not.mp hz₁'`. Establish `hz₂` using `not_not.mp hz₂'`. Take `⟨L, hL⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * 2)` from `⟨_, rfl⟩`. Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `hL2 : Real.log 2 ≤ L`.

Rewrite using `[hL]; exact Real.log_le_log (by norm_num) (by linarith)`. Establish `hLhalf : 1 / 2 < L` using `by have := Real.log_two_gt_d9; linarith`. Establish `hL0 : 0 < L` using `by linarith`. Establish `hAL0 : 0 < 20 * A * L` using `mul_pos (mul_pos (by norm_num) hA0) hL0`. Take `⟨e, he⟩ : ∃ e : ℝ, e = 1 / (20 * A * L)` from `⟨_, rfl⟩`.

Establish `he0 : 0 < e` using `by rw [he]; exact one_div_pos.mpr hAL0`. Establish `hE : 20 * A * L * e = 1` using `by rw [he]; exact mul_one_div_cancel hAL0.ne'`. Establish `hAL : A * L = 3 * |C| * L + 2 * C' * L + L` using `by rw [hA]; ring`. Establish `hAL10 : 10 ≤ 20 * A * L` using `by nlinarith`. Establish `he10 : e ≤ 1 / 10`.

Use `mul_le_mul_of_nonneg_left hAL10 he0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hreg : ∀ β : ℝ, InRegion (1 / (20 * A)) q (β : ℂ) → 1 - e ≤ β`. Introduce `β hr`. Simplify using `only [InRegion, Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add] at hr`.

Establish `: 1 / (20 * A) / Real.log ((q : ℝ) * 2) = e` using `by rw [he, hL, div_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hσ : (1 : ℝ) < 1 + 2 * e` using `by linarith`. Establish `hσ6 : 1 + 2 * e ≤ 6 / 5` using `by linarith`. Establish `hβlt : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ, DirichletCharacter.LFunction χ (β : ℂ) = 0 → β < 1`.

Introduce `χ hχ β hz`. Assume the negation of the conclusion as `h`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using not_lt.mp h) hz`. Establish `hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ, InRegion (1 / (20 * A)) q (β : ℂ) → DirichletCharacter.LFunction χ (β : ℂ) = 0 → (negLD χ ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L - 20 * A * L / 3`. Introduce `χ hχ β hr hz`.

Establish `hb1` using `hβlt χ hχ β hz`. Establish `hb0` using `hreg β hr`. Take `⟨Z, m, hZ, hm, -, hb⟩` from `hC q χ hχ 0`. Establish `key` using `re_negLogDeriv_le_of_real_zero C χ hχ Z m hZ hm β (1 + 2 * e) hσ (by linarith) (by linarith) hb1 hz (hb (1 + 2 * e) hσ hσ6)`. Rewrite `key` using `[← hL]`.

Establish `h3 : 1 / (3 * e) = 20 * A * L / 3`. Rewrite using `[div_eq_iff (mul_pos (by norm_num) he0).ne']`. Take the linear combination `-hE`. Establish `hinv : 1 / (3 * e) ≤ 1 / (1 + 2 * e - β)` using `one_div_le_one_div_of_le (by linarith) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h0b : (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ)).re ≤ 10 * A * L + C'`. Establish `h` using `hC' q 1 ((1 + 2 * e : ℝ) : ℂ) (by rw [Complex.ofReal_re]; exact hσ)`. Rewrite `h` using `[Complex.ofReal_re]`. Establish `h2 : 1 / (1 + 2 * e - 1) = 10 * A * L`. Rewrite using `[div_eq_iff (show (0 : ℝ) < 1 + 2 * e - 1 by linarith).ne']`.

Take the linear combination `-hE`. Rewrite `h` using `[h2]`. Use `Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h12ne : χ₁ * χ₂ ≠ 1`.

Introduce `h`. Apply `h12` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `h12b : (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L`. Take `⟨Z, m, hZ, -, -, hb⟩` from `hC q (χ₁ * χ₂) h12ne 0`.

Establish `hb'` using `hb (1 + 2 * e) hσ hσ6`. Establish `hs` using `sum_re_one_div_sub_zero_nonneg (χ₁ * χ₂) h12ne Z m (fun ρ hρ => ((hZ ρ).1 hρ).2) (1 + 2 * e) hσ`. Establish `hs0 : (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 2 * e : ℝ) : ℂ)` using `by simp`. Establish `hl : (negLD (χ₁ * χ₂) (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)).re = (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re` using `by rw [hs0]`. Establish `h02 : |(0 : ℝ)| + 2 = 2` using `by norm_num`.

Rewrite `hb'` using `[h02, ← hL]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos` using `(hPos q (1 + 2 * e) hσ).2.2 χ₁ χ₂ h₁ h₂`. Establish `k1` using `hbound χ₁ h₁1 β₁ hr₁ hz₁`. Establish `k2` using `hbound χ₂ h₂1 β₂ hr₂ hz₂`.

Establish `hCL : C * L ≤ |C| * L` using `mul_le_mul_of_nonneg_right (le_abs_self C) hL0.le`. Establish `hC'L : C' * (1 / 2) ≤ C' * L` using `mul_le_mul_of_nonneg_left hLhalf.le hC'0`. Establish `hCL0 : 0 ≤ |C| * L` using `mul_nonneg (abs_nonneg C) hL0.le`. Establish `hC'L0 : 0 ≤ C' * L` using `mul_nonneg hC'0 hL0.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem twoRealCharNoCommonZeroOfBounds : TwoRealOf := by
  intro hZS hLD hPos
  obtain ⟨C, hC⟩ := hZS
  obtain ⟨C', hC'0, hC'⟩ := hLD
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 3 * |C| + 2 * C' + 1 := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by have := abs_nonneg C; linarith
  have hA0 : 0 < A := by linarith
  refine ⟨1 / (20 * A), one_div_pos.mpr (mul_pos (by norm_num) hA0), ?_⟩
  intro q hq0 χ₁ χ₂ h₁ h₂ h₁1 h₂1 h12 β₁ β₂ hr₁ hr₂
  by_contra hcon
  obtain ⟨hz₁', hz₂'⟩ := not_or.mp hcon
  have hz₁ := not_not.mp hz₁'
  have hz₂ := not_not.mp hz₂'
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * 2) := ⟨_, rfl⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL2 : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) (by linarith)
  have hLhalf : 1 / 2 < L := by have := Real.log_two_gt_d9; linarith
  have hL0 : 0 < L := by linarith
  have hAL0 : 0 < 20 * A * L := mul_pos (mul_pos (by norm_num) hA0) hL0
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 / (20 * A * L) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact one_div_pos.mpr hAL0
  have hE : 20 * A * L * e = 1 := by rw [he]; exact mul_one_div_cancel hAL0.ne'
  have hAL : A * L = 3 * |C| * L + 2 * C' * L + L := by rw [hA]; ring
  have hAL10 : 10 ≤ 20 * A * L := by nlinarith
  have he10 : e ≤ 1 / 10 := by
    have := mul_le_mul_of_nonneg_left hAL10 he0.le
    linarith
  have hreg : ∀ β : ℝ, InRegion (1 / (20 * A)) q (β : ℂ) → 1 - e ≤ β := by
    intro β hr
    simp only [InRegion, Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add] at hr
    have : 1 / (20 * A) / Real.log ((q : ℝ) * 2) = e := by rw [he, hL, div_div]
    linarith
  have hσ : (1 : ℝ) < 1 + 2 * e := by linarith
  have hσ6 : 1 + 2 * e ≤ 6 / 5 := by linarith
  have hβlt : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β < 1 := by
    intro χ hχ β hz
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using not_lt.mp h) hz
  have hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      InRegion (1 / (20 * A)) q (β : ℂ) → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      (negLD χ ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L - 20 * A * L / 3 := by
    intro χ hχ β hr hz
    have hb1 := hβlt χ hχ β hz
    have hb0 := hreg β hr
    obtain ⟨Z, m, hZ, hm, -, hb⟩ := hC q χ hχ 0
    have key := re_negLogDeriv_le_of_real_zero C χ hχ Z m hZ hm β (1 + 2 * e) hσ
      (by linarith) (by linarith) hb1 hz (hb (1 + 2 * e) hσ hσ6)
    rw [← hL] at key
    have h3 : 1 / (3 * e) = 20 * A * L / 3 := by
      rw [div_eq_iff (mul_pos (by norm_num) he0).ne']
      linear_combination -hE
    have hinv : 1 / (3 * e) ≤ 1 / (1 + 2 * e - β) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have h0b : (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ)).re ≤ 10 * A * L + C' := by
    have h := hC' q 1 ((1 + 2 * e : ℝ) : ℂ) (by rw [Complex.ofReal_re]; exact hσ)
    rw [Complex.ofReal_re] at h
    have h2 : 1 / (1 + 2 * e - 1) = 10 * A * L := by
      rw [div_eq_iff (show (0 : ℝ) < 1 + 2 * e - 1 by linarith).ne']
      linear_combination -hE
    rw [h2] at h
    have := Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ))
    linarith
  have h12ne : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply h12
    calc χ₁ = χ₁ * χ₂ ^ 2 := by rw [h₂, mul_one]
      _ = χ₁ * χ₂ * χ₂ := by rw [pow_two, mul_assoc]
      _ = χ₂ := by rw [h, one_mul]
  have h12b : (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L := by
    obtain ⟨Z, m, hZ, -, -, hb⟩ := hC q (χ₁ * χ₂) h12ne 0
    have hb' := hb (1 + 2 * e) hσ hσ6
    have hs := sum_re_one_div_sub_zero_nonneg (χ₁ * χ₂) h12ne Z m
      (fun ρ hρ => ((hZ ρ).1 hρ).2) (1 + 2 * e) hσ
    have hs0 : (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 2 * e : ℝ) : ℂ) := by simp
    have hl : (negLD (χ₁ * χ₂) (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)).re =
        (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re := by rw [hs0]
    have h02 : |(0 : ℝ)| + 2 = 2 := by norm_num
    rw [h02, ← hL] at hb'
    linarith
  have hpos := (hPos q (1 + 2 * e) hσ).2.2 χ₁ χ₂ h₁ h₂
  have k1 := hbound χ₁ h₁1 β₁ hr₁ hz₁
  have k2 := hbound χ₂ h₂1 β₂ hr₂ hz₂
  have hCL : C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) hL0.le
  have hC'L : C' * (1 / 2) ≤ C' * L := mul_le_mul_of_nonneg_left hLhalf.le hC'0
  have hCL0 : 0 ≤ |C| * L := mul_nonneg (abs_nonneg C) hL0.le
  have hC'L0 : 0 ≤ C' * L := mul_nonneg hC'0 hL0.le
  linarith

end Formalism.ZeroFreeDirichlet
