import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroBand

/- English proof (translation)
Use `Set.Finite.subset ((Finset.Icc ⌊-T⌋ ⌊T⌋).finite_toSet.biUnion fun k _ => hW (k : ℝ)) ?_` and prove the remaining obligations. Introduce and unpack `ρ ⟨h0, h1, h2, h3⟩`. Rewrite `h2` using `[abs_lt]`. Use `Set.mem_iUnion₂.2 ⟨⌊ρ.im⌋, ?_, h0, h1, ?_, h3⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_Icc, Set.mem_Icc]`.

Conclude with `⟨Int.floor_mono h2.1.le, Int.floor_mono h2.2.le⟩`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im]`.
-/
theorem finite_box (f : ℂ → ℂ)
    (hW : ∀ t : ℝ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}.Finite) (T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ f ρ = 0}.Finite := by
  refine Set.Finite.subset
    ((Finset.Icc ⌊-T⌋ ⌊T⌋).finite_toSet.biUnion fun k _ => hW (k : ℝ)) ?_
  rintro ρ ⟨h0, h1, h2, h3⟩
  rw [abs_lt] at h2
  refine Set.mem_iUnion₂.2 ⟨⌊ρ.im⌋, ?_, h0, h1, ?_, h3⟩
  · rw [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Int.floor_mono h2.1.le, Int.floor_mono h2.2.le⟩
  · rw [abs_le]
    constructor <;> linarith [Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im]

/- English proof (translation)
Establish `hu0 : 0 < u` using `by linarith`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hρ : T ≤ ‖ρ‖` using `h2.trans (Complex.abs_im_le_norm ρ)`. Establish `hρ0 : 0 < ‖ρ‖` using `hT0.trans_le hρ`. Rewrite using `[norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]`.

Apply `mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)` to reduce the goal to its premises. Establish `hup : u ^ ρ.re ≤ u`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_term_le (m : ℕ) {u T : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) {ρ : ℂ} (h1 : ρ.re < 1)
    (h2 : T ≤ |ρ.im|) : ‖(m : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (m : ℝ) * (u / T) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hρ : T ≤ ‖ρ‖ := h2.trans (Complex.abs_im_le_norm ρ)
  have hρ0 : 0 < ‖ρ‖ := hT0.trans_le hρ
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  have hup : u ^ ρ.re ≤ u := by
    calc u ^ ρ.re ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) h1.le
      _ = u := Real.rpow_one u
  calc u ^ ρ.re / ‖ρ‖ ≤ u / ‖ρ‖ := div_le_div_of_nonneg_right hup hρ0.le
    _ ≤ u / T := div_le_div_of_nonneg_left hu0.le hT0 hρ

/- English proof (translation)
Establish `hT0 : 0 < T` using `by linarith`. Establish `hS'` using `finite_box f (fun t => (hW t).1) T'`. Establish `hS` using `finite_box f (fun t => (hW t).1) T`. Establish `hA` using `(hW T).1`. Establish `hA'` using `(hW (-T)).1`.

Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hS', finsum_mem_eq_finite_toFinset_sum _ hS]`. Establish `hsub : hS.toFinset ⊆ hS'.toFinset`. Introduce `ρ hρ`. Rewrite `hρ`, the goal using `[Set.Finite.mem_toFinset]`. Take `⟨a, b, c, d⟩` from `hρ`.

Conclude with `⟨a, b, c.trans_le hT1, d⟩`. Rewrite using `[← Finset.sum_sdiff hsub, add_sub_cancel_right]`. Establish `hD : ∀ ρ ∈ hS'.toFinset \ hS.toFinset, ρ ∈ hA.toFinset ∪ hA'.toFinset ∧ ρ.re < 1 ∧ T ≤ |ρ.im|`. Introduce `ρ hρ`. Take `⟨h1, h2⟩` from `Finset.mem_sdiff.1 hρ`.

Rewrite `h1`, `h2` using `[Set.Finite.mem_toFinset]`. Take `⟨a, b, c, d⟩` from `h1`. Establish `hT' : T ≤ |ρ.im|` using `not_lt.1 fun h => h2 ⟨a, b, h, d⟩`. Use `⟨?_, b, hT'⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]`.

Rewrite `c` using `[abs_lt]`. Break down `le_or_gt 0 ρ.im with h | h` into its components or cases. Use `left`. Rewrite `hT'` using `[abs_of_nonneg h]`. Use `⟨a, b, ?_, d⟩` and prove the remaining obligations.

Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Use `right`. Rewrite `hT'` using `[abs_of_neg h]`. Use `⟨a, b, ?_, d⟩` and prove the remaining obligations.

Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `hm : ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ) ≤ B T + B (-T)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_union_inter]`.

Conclude with `le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)`. Use `_ ≤ B T + B (-T) := by`. Rewrite using `[← finsum_mem_eq_finite_toFinset_sum _ hA, ← finsum_mem_eq_finite_toFinset_sum _ hA']`. Conclude with `add_le_add (hW T).2 (hW (-T)).2`. Combine the equalities or inequalities in the displayed calculation.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)` and prove the remaining obligations. Take `⟨-, h1, h2⟩` from `hD ρ hρ`. Conclude with `norm_term_le (m ρ) hT hu h1 h2`. Use `_ = (∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ)) * (u / T) := by rw [Finset.sum_mul]`. Use `_ ≤ (B T + B (-T)) * (u / T) := mul_le_mul_of_nonneg_right hm (div_nonneg (by linarith) hT0.le)`.
-/
theorem band_le (f : ℂ → ℂ) (m : ℂ → ℕ) (B : ℝ → ℝ)
    (hW : ∀ t : ℝ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}.Finite ∧
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}, (m ρ : ℝ) ≤ B t)
    {u T T' : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) (hT1 : T ≤ T') (hT2 : T' ≤ T + 1) :
    ‖(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (B T + B (-T)) * (u / T) := by
  classical
  have hT0 : 0 < T := by linarith
  have hS' := finite_box f (fun t => (hW t).1) T'
  have hS := finite_box f (fun t => (hW t).1) T
  have hA := (hW T).1
  have hA' := (hW (-T)).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS', finsum_mem_eq_finite_toFinset_sum _ hS]
  have hsub : hS.toFinset ⊆ hS'.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨a, b, c, d⟩ := hρ
    exact ⟨a, b, c.trans_le hT1, d⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hD : ∀ ρ ∈ hS'.toFinset \ hS.toFinset,
      ρ ∈ hA.toFinset ∪ hA'.toFinset ∧ ρ.re < 1 ∧ T ≤ |ρ.im| := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hρ
    rw [Set.Finite.mem_toFinset] at h1 h2
    obtain ⟨a, b, c, d⟩ := h1
    have hT' : T ≤ |ρ.im| := not_lt.1 fun h => h2 ⟨a, b, h, d⟩
    refine ⟨?_, b, hT'⟩
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    rw [abs_lt] at c
    rcases le_or_gt 0 ρ.im with h | h
    · left
      rw [abs_of_nonneg h] at hT'
      refine ⟨a, b, ?_, d⟩
      rw [abs_le]
      constructor <;> linarith
    · right
      rw [abs_of_neg h] at hT'
      refine ⟨a, b, ?_, d⟩
      rw [abs_le]
      constructor <;> linarith
  have hm : ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ) ≤ B T + B (-T) := by
    calc ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ)
        ≤ ∑ ρ ∈ hA.toFinset ∪ hA'.toFinset, (m ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => (hD ρ hρ).1)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ hA.toFinset, (m ρ : ℝ) + ∑ ρ ∈ hA'.toFinset, (m ρ : ℝ) := by
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      _ ≤ B T + B (-T) := by
          rw [← finsum_mem_eq_finite_toFinset_sum _ hA, ← finsum_mem_eq_finite_toFinset_sum _ hA']
          exact add_le_add (hW T).2 (hW (-T)).2
  calc _ ≤ ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ) * (u / T) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
        obtain ⟨-, h1, h2⟩ := hD ρ hρ
        exact norm_term_le (m ρ) hT hu h1 h2
    _ = (∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ)) * (u / T) := by rw [Finset.sum_mul]
    _ ≤ (B T + B (-T)) * (u / T) :=
        mul_le_mul_of_nonneg_right hm (div_nonneg (by linarith) hT0.le)

/- English proof (translation)
Take `⟨C, hC, hcount⟩` from `GlobalTheory.ZeroWindow.count_zeros_window`. Use `⟨2 * C, by linarith, ?_⟩` and prove the remaining obligations. Introduce `N _ χ hχ u T T' hT hu hT1 hT2`. Establish `hw` using `hcount N χ hχ`. Use `⟨finite_box _ (fun t => (hw t).1) T, ?_⟩` and prove the remaining obligations.

Use `(band_le (LFunction χ) (fun ρ => analyticOrderNatAt (LFunction χ) ρ) (fun t => C * Real.log (N * (|t| + 2))) hw hT hu hT1 hT2).trans ?_` and prove the remaining obligations. Establish `hT0 : 0 < T` using `by linarith`. Rewrite using `[abs_neg, abs_of_pos hT0]`. Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)`. Establish `huT : T + 2 ≤ u * T` using `by nlinarith`.

Establish `hx : (N : ℝ) * (T + 2) ≤ N * u * T`. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left huT (by linarith)`. Establish `hpos : 0 < (N : ℝ) * (T + 2)` using `by positivity`. Establish `hL1 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T)` using `Real.log_le_log hpos hx`.

Establish `h4 : (4 : ℝ) ≤ N * u * T` using `by nlinarith`. Establish `hL : 1 ≤ Real.log (N * u * T)`. Establish `he : Real.exp 1 < 4` using `by have := Real.exp_one_lt_d9; linarith`. Conclude with `((Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith)).le`. Establish `hL2 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T) ^ 2` using `hL1.trans (by nlinarith)`.

Establish `hq : 0 ≤ u / T` using `div_nonneg (by linarith) hT0.le`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem zeros_band : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 → {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite ∧ ‖(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)) - ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T) := by
  obtain ⟨C, hC, hcount⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨2 * C, by linarith, ?_⟩
  intro N _ χ hχ u T T' hT hu hT1 hT2
  have hw := hcount N χ hχ
  refine ⟨finite_box _ (fun t => (hw t).1) T, ?_⟩
  refine (band_le (LFunction χ) (fun ρ => analyticOrderNatAt (LFunction χ) ρ)
    (fun t => C * Real.log (N * (|t| + 2))) hw hT hu hT1 hT2).trans ?_
  have hT0 : 0 < T := by linarith
  rw [abs_neg, abs_of_pos hT0]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have huT : T + 2 ≤ u * T := by nlinarith
  have hx : (N : ℝ) * (T + 2) ≤ N * u * T := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left huT (by linarith)
  have hpos : 0 < (N : ℝ) * (T + 2) := by positivity
  have hL1 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T) := Real.log_le_log hpos hx
  have h4 : (4 : ℝ) ≤ N * u * T := by nlinarith
  have hL : 1 ≤ Real.log (N * u * T) := by
    have he : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
    exact ((Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith)).le
  have hL2 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T) ^ 2 := hL1.trans (by nlinarith)
  have hq : 0 ≤ u / T := div_nonneg (by linarith) hT0.le
  calc (C * Real.log (N * (T + 2)) + C * Real.log (N * (T + 2))) * (u / T)
      = 2 * C * Real.log (N * (T + 2)) * (u / T) := by ring
    _ ≤ 2 * C * Real.log (N * u * T) ^ 2 * (u / T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2 (by linarith)) hq
    _ = 2 * C * (u * Real.log (N * u * T) ^ 2 / T) := by ring

end GlobalTheory.ZeroBand
