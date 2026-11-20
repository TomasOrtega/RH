import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

namespace Elem

def primeWeight (B : ℝ) (i : ℕ) : ℝ := if i.Prime ∧ B < i then Real.log i else 0

/- English proof (translation)
Unfold `primeWeight`. Use `split_ifs`. Conclude with `Real.log_natCast_nonneg i`. Conclude with `le_rfl`.
-/
theorem primeWeight_nonneg (B : ℝ) (i : ℕ) : 0 ≤ primeWeight B i := by
  unfold primeWeight
  split_ifs
  · exact Real.log_natCast_nonneg i
  · exact le_rfl

/- English proof (translation)
Establish `hθ` using `ChebyshevThetaBound.intersectionNumber_baseChange (K : ℝ) (Nat.cast_nonneg K)`. Rewrite `hθ` using `[Nat.floor_natCast]`. Use `le_trans ?_ hθ` and prove the remaining obligations. Rewrite using `[Finset.sum_filter]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `i _`. Unfold `primeWeight`. Use `split_ifs with h1 h2 h2`. Conclude with `le_rfl`. Conclude with `absurd h1.1 h2`.

Conclude with `Real.log_natCast_nonneg i`. Conclude with `le_rfl`.
-/
theorem sum_primeWeight_le (B : ℝ) (K : ℕ) :
    ∑ i ∈ range (K + 1), primeWeight B i ≤ K * Real.log 4 := by
  have hθ := ChebyshevThetaBound.intersectionNumber_baseChange (K : ℝ) (Nat.cast_nonneg K)
  rw [Nat.floor_natCast] at hθ
  refine le_trans ?_ hθ
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  unfold primeWeight
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd h1.1 h2
  · exact Real.log_natCast_nonneg i
  · exact le_rfl

/- English proof (translation)
Unfold `primeWeight`. Rewrite using `[if_neg]`. Introduce and unpack `⟨_, h⟩`. Establish `: (i : ℝ) ≤ B`. Use `Nat.le_floor_iff hB |>.mp (Nat.lt_succ_iff.mp hi)` as an intermediate fact.

Conclude with `this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem primeWeight_eq_zero_of_lt (B : ℝ) (hB : 0 ≤ B) {i : ℕ} (hi : i < ⌊B⌋₊ + 1) :
    primeWeight B i = 0 := by
  unfold primeWeight
  rw [if_neg]
  rintro ⟨_, h⟩
  have : (i : ℝ) ≤ B := by
    have := Nat.le_floor_iff hB |>.mp (Nat.lt_succ_iff.mp hi)
    exact this
  linarith

/- English proof (translation)
Use `set M := ⌊B⌋₊ + 1 with hM`. Proceed by induction on `j with`. Consider the case `zero`. Establish `h0 : ∀ i ∈ range (M + 0), primeWeight B i = 0` using `fun i hi => primeWeight_eq_zero_of_lt B hB.le (by have := Finset.mem_range.mp hi; omega)`. Rewrite using `[Finset.sum_eq_zero (fun i hi => by rw [h0 i hi, zero_div]), Finset.sum_eq_zero h0]`.

Simplify using the standard rewrite rules. Consider the case `succ j ih => set K := M + j with hK`. Establish `hK1 : (1 : ℝ) ≤ K`. Establish `: 1 ≤ K` using `by omega`. Conclude with `this` after adjusting the coercions.

Establish `hKpos : (0 : ℝ) < K` using `by linarith`. Rewrite `*` using `[show M + (j + 1) = K + 1 by omega]`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ]`. Use `set S := ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2`. Use `set G := ∑ i ∈ range K, primeWeight B i`.

Use `set g := primeWeight B K`. Establish `hG1 : G + g ≤ K * Real.log 4`. Use `sum_primeWeight_le B K` as an intermediate fact. Rewrite `this` using `[Finset.sum_range_succ]`. Conclude with `this`.

Establish `hG1nn : 0 ≤ G + g`. Establish `: 0 ≤ ∑ i ∈ range (K + 1), primeWeight B i` using `Finset.sum_nonneg (fun i _ => primeWeight_nonneg B i)`. Rewrite `this` using `[Finset.sum_range_succ]`. Conclude with `this`. Establish `hlog4 : 0 ≤ Real.log 4` using `Real.log_nonneg (by norm_num)`.

Move the coercions through the operations in `at ih ⊢`. Establish `hdiff : (S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2) - (S - G / (K : ℝ) ^ 2) = (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hnn : 0 ≤ 1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2`.

Rewrite using `[sub_nonneg]`. Apply `one_div_le_one_div_of_le (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hstep : (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) ≤ 2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1))`. Combine the equalities or inequalities in the displayed calculation.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ Real.log 4 * (2 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1))) := by`. Apply `mul_le_mul_of_nonneg_left _ hlog4` to reduce the goal to its premises. Rewrite using `[show (2 : ℝ) * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) = 2 / (K * ((K : ℝ) + 1)) by field_simp; ring]`.

Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Use `_ = 2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by ring`. Establish `ih' : S - G / (K : ℝ) ^ 2 ≤ 2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / (K : ℝ))`. Simplify using `using ih`.

Establish `: S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2 ≤ 2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / ((K : ℝ) + 1))`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `using this`.
-/
theorem abel_step (B : ℝ) (hB : 0 < B) (j : ℕ) :
    (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i / (i : ℝ) ^ 2) -
        (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i) / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ) ^ 2 ≤
      2 * Real.log 4 * (1 / ((⌊B⌋₊ + 1 : ℕ) : ℝ) - 1 / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ)) := by
  set M := ⌊B⌋₊ + 1 with hM
  induction j with
  | zero =>
    have h0 : ∀ i ∈ range (M + 0), primeWeight B i = 0 := fun i hi =>
      primeWeight_eq_zero_of_lt B hB.le (by have := Finset.mem_range.mp hi; omega)
    rw [Finset.sum_eq_zero (fun i hi => by rw [h0 i hi, zero_div]),
      Finset.sum_eq_zero h0]
    simp
  | succ j ih =>
    set K := M + j with hK
    have hK1 : (1 : ℝ) ≤ K := by
      have : 1 ≤ K := by omega
      exact_mod_cast this
    have hKpos : (0 : ℝ) < K := by linarith
    rw [show M + (j + 1) = K + 1 by omega] at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    set S := ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
    set G := ∑ i ∈ range K, primeWeight B i
    set g := primeWeight B K
    have hG1 : G + g ≤ K * Real.log 4 := by
      have := sum_primeWeight_le B K
      rw [Finset.sum_range_succ] at this
      exact this
    have hG1nn : 0 ≤ G + g := by
      have : 0 ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
        Finset.sum_nonneg (fun i _ => primeWeight_nonneg B i)
      rw [Finset.sum_range_succ] at this
      exact this
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    push_cast at ih ⊢

    have hdiff : (S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2) -
        (S - G / (K : ℝ) ^ 2) = (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) := by
      field_simp
      ring
    have hnn : 0 ≤ 1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2 := by
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hstep : (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) ≤
        2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by
      calc (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2)
          ≤ (K * Real.log 4) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_right hG1 hnn
        _ = Real.log 4 * ((2 * K + 1) / (K * ((K : ℝ) + 1) ^ 2)) := by
            field_simp
            ring
        _ ≤ Real.log 4 * (2 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left _ hlog4
            rw [show (2 : ℝ) * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) = 2 / (K * ((K : ℝ) + 1)) by
              field_simp; ring]
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
        _ = 2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by ring
    have ih' : S - G / (K : ℝ) ^ 2 ≤ 2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / (K : ℝ)) := by
      simpa using ih
    have : S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2 ≤
        2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / ((K : ℝ) + 1)) := by
      linarith
    simpa using this

/- English proof (translation)
Use `set M := ⌊B⌋₊ + 1 with hM`. Establish `hlog4 : 0 ≤ Real.log 4` using `Real.log_nonneg (by norm_num)`. Establish `hMB : B < (M : ℝ)`. Rewrite using `[hM]`. Use `push_cast`.

Conclude with `Nat.lt_floor_add_one B`. Establish `hMpos : (0 : ℝ) < M` using `lt_trans hB hMB`. Establish `hfinal : 2 * Real.log 4 / (M : ℝ) ≤ 2 * Real.log 4 / B` using `div_le_div_of_nonneg_left (by positivity) hB hMB.le`. Break down `lt_or_ge K M with hK | hK` into its components or cases. Rewrite using `[Finset.sum_eq_zero]`.

Check the signs of the components of the expression. Introduce `i hi`. Rewrite using `[primeWeight_eq_zero_of_lt B hB.le (lt_trans (Finset.mem_range.mp hi) hK), zero_div]`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hK`. Establish `hW` using `abel_step B hB j`.

Rewrite `hW` using `[← hM]`. Use `set K := M + j`. Establish `hKpos : (0 : ℝ) < (K : ℝ)`. Establish `: (M : ℝ) ≤ K` using `by exact_mod_cast (Nat.le_add_right M j)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hG : ∑ i ∈ range K, primeWeight B i ≤ K * Real.log 4`. Combine the equalities or inequalities in the displayed calculation. Establish `hGK : (∑ i ∈ range K, primeWeight B i) / (K : ℝ) ^ 2 ≤ Real.log 4 / K`. Rewrite using `[div_le_div_iff₀ (by positivity) hKpos]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h1 : 0 ≤ Real.log 4 / K` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prime_partial_le (B : ℝ) (hB : 0 < B) (K : ℕ) :
    ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by
  set M := ⌊B⌋₊ + 1 with hM
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hMB : B < (M : ℝ) := by
    rw [hM]; push_cast; exact Nat.lt_floor_add_one B
  have hMpos : (0 : ℝ) < M := lt_trans hB hMB
  have hfinal : 2 * Real.log 4 / (M : ℝ) ≤ 2 * Real.log 4 / B :=
    div_le_div_of_nonneg_left (by positivity) hB hMB.le
  rcases lt_or_ge K M with hK | hK
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro i hi
      rw [primeWeight_eq_zero_of_lt B hB.le (lt_trans (Finset.mem_range.mp hi) hK), zero_div]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
    have hW := abel_step B hB j
    rw [← hM] at hW
    set K := M + j
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : (M : ℝ) ≤ K := by exact_mod_cast (Nat.le_add_right M j)
      linarith
    have hG : ∑ i ∈ range K, primeWeight B i ≤ K * Real.log 4 := by
      calc ∑ i ∈ range K, primeWeight B i ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun i _ _ => primeWeight_nonneg B i)
        _ ≤ K * Real.log 4 := sum_primeWeight_le B K
    have hGK : (∑ i ∈ range K, primeWeight B i) / (K : ℝ) ^ 2 ≤ Real.log 4 / K := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      nlinarith
    have h1 : 0 ≤ Real.log 4 / K := by positivity
    calc ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
        ≤ 2 * Real.log 4 * (1 / (M : ℝ) - 1 / (K : ℝ)) + Real.log 4 / K := by linarith
      _ = 2 * Real.log 4 / (M : ℝ) - Real.log 4 / K := by ring
      _ ≤ 2 * Real.log 4 / (M : ℝ) := by linarith
      _ ≤ 2 * Real.log 4 / B := hfinal

end Elem

open Elem in

/- English proof (translation)
Introduce `B hB`. Use `set s : Set ℕ := {p | p.Prime ∧ B < p}`. Establish `hind : s.indicator (fun p : ℕ => Real.log p / (p : ℝ) ^ 2) = fun i => primeWeight B i / (i : ℝ) ^ 2`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i.Prime ∧ B < i`.

Simplify using `[s, Set.indicator_of_mem, h, primeWeight]`. Simplify using `[s, Set.indicator_of_notMem, h, primeWeight]`. Establish `hnn : ∀ i, 0 ≤ primeWeight B i / (i : ℝ) ^ 2` using `fun i => div_nonneg (primeWeight_nonneg B i) (by positivity)`. Establish `hsum : Summable (fun i => primeWeight B i / (i : ℝ) ^ 2)` using `summable_of_sum_range_le hnn (prime_partial_le B hB)`. Establish `hsub : Summable (fun p : s => Real.log p / (p : ℝ) ^ 2)`.

Use `(summable_subtype_iff_indicator (f := fun p : ℕ => Real.log p / (p : ℝ) ^ 2) (s := s)).mpr (by rw [hind]; exact hsum)` as an intermediate fact. Conclude with `this`. Use `⟨hsub, ?_⟩` and prove the remaining obligations. Establish `: ∑' p : s, Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / B`. Rewrite using `[tsum_subtype s (fun p : ℕ => Real.log p / (p : ℝ) ^ 2), hind]`.

Conclude with `Real.tsum_le_of_sum_range_le hnn (prime_partial_le B hB)`. Conclude with `this`.
-/
theorem PrimeLogSquareTail.intersectionNumber_baseChange : PrimeLogSquareTail.Statement := by
  intro B hB
  set s : Set ℕ := {p | p.Prime ∧ B < p}
  have hind : s.indicator (fun p : ℕ => Real.log p / (p : ℝ) ^ 2) =
      fun i => primeWeight B i / (i : ℝ) ^ 2 := by
    funext i
    by_cases h : i.Prime ∧ B < i
    · simp [s, Set.indicator_of_mem, h, primeWeight]
    · simp [s, Set.indicator_of_notMem, h, primeWeight]
  have hnn : ∀ i, 0 ≤ primeWeight B i / (i : ℝ) ^ 2 := fun i =>
    div_nonneg (primeWeight_nonneg B i) (by positivity)
  have hsum : Summable (fun i => primeWeight B i / (i : ℝ) ^ 2) :=
    summable_of_sum_range_le hnn (prime_partial_le B hB)
  have hsub : Summable (fun p : s => Real.log p / (p : ℝ) ^ 2) := by
    have := (summable_subtype_iff_indicator (f := fun p : ℕ => Real.log p / (p : ℝ) ^ 2)
      (s := s)).mpr (by rw [hind]; exact hsum)
    exact this
  refine ⟨hsub, ?_⟩
  have : ∑' p : s, Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by
    rw [tsum_subtype s (fun p : ℕ => Real.log p / (p : ℝ) ^ 2), hind]
    exact Real.tsum_le_of_sum_range_le hnn (prime_partial_le B hB)
  exact this

namespace Elem

def phiT (t : ℝ) : ℝ := (1 + Real.log t) / t

/- English proof (translation)
Unfold `phiT`. Use `Real.log_nonneg ht` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem phiT_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ phiT t := by
  unfold phiT
  have := Real.log_nonneg ht
  positivity

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Use `set L := Real.log (x + 1)`. Use `set l := Real.log x`. Establish `hlL : L - 1 / x ≤ l`. Establish `h` using `Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)`.

Rewrite `h` using `[Real.log_div (by linarith) hx0.ne']`. Establish `: (x + 1) / x - 1 = 1 / x` using `by field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL : 1 + 1 / x ≤ L`. Establish `h2` using `Real.log_two_gt_d9`.

Establish `h4 : Real.log 4 ≤ L` using `Real.log_le_log (by norm_num) (by linarith)`. Establish `: Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring`. Establish `h13 : 1 / x ≤ 1 / 3` using `one_div_le_one_div_of_le (by norm_num) hx`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmain : (1 + (L - 1 / x)) / x - (1 + L) / (x + 1) - L / (x + 1) ^ 2 = (L * x - x - 1) / (x ^ 2 * (x + 1) ^ 2)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hnum : 0 ≤ L * x - x - 1`. Establish `: (1 + 1 / x) * x = x + 1` using `by field_simp`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : (1 + (L - 1 / x)) / x ≤ (1 + l) / x` using `div_le_div_of_nonneg_right (by linarith) hx0.le`. Establish `h2 : 0 ≤ (L * x - x - 1) / (x ^ 2 * (x + 1) ^ 2)` using `by positivity`. Unfold `phiT`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_div_sq_le_phiT_sub (x : ℝ) (hx : 3 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ 2 ≤ phiT x - phiT (x + 1) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log (x + 1)
  set l := Real.log x
  have hlL : L - 1 / x ≤ l := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by linarith) hx0.ne'] at h
    have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have hL : 1 + 1 / x ≤ L := by
    have h2 := Real.log_two_gt_d9
    have h4 : Real.log 4 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h13 : 1 / x ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hx
    linarith
  have hmain : (1 + (L - 1 / x)) / x - (1 + L) / (x + 1) - L / (x + 1) ^ 2 =
      (L * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) := by
    field_simp
    ring
  have hnum : 0 ≤ L * x - x - 1 := by
    have : (1 + 1 / x) * x = x + 1 := by field_simp
    nlinarith
  have h1 : (1 + (L - 1 / x)) / x ≤ (1 + l) / x :=
    div_le_div_of_nonneg_right (by linarith) hx0.le
  have h2 : 0 ≤ (L * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) := by positivity
  unfold phiT
  linarith

def intWeight (B₀ : ℝ) (m : ℕ) : ℝ := if B₀ < m then Real.log m / (m : ℝ) ^ 2 else 0

/- English proof (translation)
Unfold `intWeight`. Use `split_ifs`. Conclude with `div_nonneg (Real.log_natCast_nonneg m) (by positivity)`. Conclude with `le_rfl`.
-/
theorem intWeight_nonneg (B₀ : ℝ) (m : ℕ) : 0 ≤ intWeight B₀ m := by
  unfold intWeight
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg m) (by positivity)
  · exact le_rfl

/- English proof (translation)
Use `set n := ⌊B₀⌋₊ with hn`. Establish `hn16 : 16 ≤ n`. Rewrite using `[hn]; exact Nat.le_floor (by exact_mod_cast hB)`. Proceed by induction on `j with`. Consider the case `zero`.

Rewrite using `[Finset.sum_eq_zero]`. Simplify using the standard rewrite rules. Introduce `m hm`. Establish `hm' : m ≤ n` using `by have := Finset.mem_range.mp hm; omega`. Unfold `intWeight`.

Rewrite using `[if_neg]`. Introduce `h`. Establish `: (m : ℝ) ≤ B₀`. Use `(Nat.le_floor_iff (by linarith)).mp hm'` as an intermediate fact. Conclude with `this`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ j ih`. Rewrite using `[show n + 1 + (j + 1) = (n + 1 + j) + 1 by omega, Finset.sum_range_succ]`. Establish `hw : intWeight B₀ (n + 1 + j) = Real.log ((n + j : ℕ) + 1 : ℝ) / (((n + j : ℕ) : ℝ) + 1) ^ 2`. Unfold `intWeight`.

Rewrite using `[if_pos]`. Use `push_cast`. Put the polynomial expressions in normal form. Establish `: B₀ < ((n + 1 : ℕ) : ℝ)`. Rewrite using `[hn]`.

Use `push_cast`. Conclude with `Nat.lt_floor_add_one B₀`. Establish `h2 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 + j : ℕ) : ℝ)` using `by exact_mod_cast (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk` using `log_div_sq_le_phiT_sub ((n + j : ℕ) : ℝ) (by have : 3 ≤ n + j := by omega`.

Conclude with `this)` after adjusting the coercions. Rewrite using `[hw]`. Establish `: ((n + (j + 1) : ℕ) : ℝ) = ((n + j : ℕ) : ℝ) + 1` using `by push_cast; ring`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem int_step (B₀ : ℝ) (hB : 16 ≤ B₀) (j : ℕ) :
    ∑ m ∈ range (⌊B₀⌋₊ + 1 + j), intWeight B₀ m ≤
      phiT (⌊B₀⌋₊ : ℝ) - phiT ((⌊B₀⌋₊ + j : ℕ) : ℝ) := by
  set n := ⌊B₀⌋₊ with hn
  have hn16 : 16 ≤ n := by
    rw [hn]; exact Nat.le_floor (by exact_mod_cast hB)
  induction j with
  | zero =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro m hm
      have hm' : m ≤ n := by have := Finset.mem_range.mp hm; omega
      unfold intWeight
      rw [if_neg]
      intro h
      have : (m : ℝ) ≤ B₀ := by
        have := (Nat.le_floor_iff (by linarith)).mp hm'
        exact this
      linarith
  | succ j ih =>
    rw [show n + 1 + (j + 1) = (n + 1 + j) + 1 by omega, Finset.sum_range_succ]
    have hw : intWeight B₀ (n + 1 + j) =
        Real.log ((n + j : ℕ) + 1 : ℝ) / (((n + j : ℕ) : ℝ) + 1) ^ 2 := by
      unfold intWeight
      rw [if_pos]
      · push_cast; ring_nf
      · have : B₀ < ((n + 1 : ℕ) : ℝ) := by
          rw [hn]; push_cast; exact Nat.lt_floor_add_one B₀
        have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 + j : ℕ) : ℝ) := by exact_mod_cast (by omega)
        linarith
    have hk := log_div_sq_le_phiT_sub ((n + j : ℕ) : ℝ)
      (by have : 3 ≤ n + j := by omega
          exact_mod_cast this)
    rw [hw]
    have : ((n + (j + 1) : ℕ) : ℝ) = ((n + j : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [this]
    linarith

/- English proof (translation)
Use `set n := ⌊B₀⌋₊ with hn`. Establish `hB0 : 0 < B₀` using `by linarith`. Establish `hn16 : 16 ≤ n`. Rewrite using `[hn]; exact Nat.le_floor (by exact_mod_cast hB)`. Establish `hnle : (n : ℝ) ≤ B₀` using `Nat.floor_le hB0.le`.

Establish `hnlt : B₀ < (n : ℝ) + 1` using `Nat.lt_floor_add_one B₀`. Establish `hn1 : (16 : ℝ) ≤ n` using `by exact_mod_cast hn16`. Establish `hphi : phiT n ≤ 2 * (1 + Real.log B₀) / B₀`. Unfold `phiT`. Establish `hlog : Real.log n ≤ Real.log B₀` using `Real.log_le_log (by linarith) hnle`.

Establish `hlogn : 0 ≤ Real.log n` using `Real.log_nonneg (by linarith)`. Rewrite using `[div_le_div_iff₀ (by linarith) hB0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hS : ∀ K, ∑ m ∈ range K, intWeight B₀ m ≤ phiT n`. Introduce `K`.

Break down `le_or_gt K (n + 1) with hK | hK` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Use `phiT_nonneg (t := ((n + 0 : ℕ) : ℝ)) (by push_cast; linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hK.le`.

Combine the equalities or inequalities in the displayed calculation. Use `phiT_nonneg (t := ((n + j : ℕ) : ℝ)) (by push_cast; linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hS K).trans hphi`.
-/
theorem int_partial_le (B₀ : ℝ) (hB : 16 ≤ B₀) (K : ℕ) :
    ∑ m ∈ range K, intWeight B₀ m ≤ 2 * (1 + Real.log B₀) / B₀ := by
  set n := ⌊B₀⌋₊ with hn
  have hB0 : 0 < B₀ := by linarith
  have hn16 : 16 ≤ n := by
    rw [hn]; exact Nat.le_floor (by exact_mod_cast hB)
  have hnle : (n : ℝ) ≤ B₀ := Nat.floor_le hB0.le
  have hnlt : B₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one B₀
  have hn1 : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hphi : phiT n ≤ 2 * (1 + Real.log B₀) / B₀ := by
    unfold phiT
    have hlog : Real.log n ≤ Real.log B₀ := Real.log_le_log (by linarith) hnle
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    rw [div_le_div_iff₀ (by linarith) hB0]
    nlinarith
  have hS : ∀ K, ∑ m ∈ range K, intWeight B₀ m ≤ phiT n := by
    intro K
    rcases le_or_gt K (n + 1) with hK | hK
    · calc ∑ m ∈ range K, intWeight B₀ m ≤ ∑ m ∈ range (n + 1 + 0), intWeight B₀ m :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun m _ _ => intWeight_nonneg B₀ m)
        _ ≤ phiT n - phiT ((n + 0 : ℕ) : ℝ) := int_step B₀ hB 0
        _ ≤ phiT n := by
            have := phiT_nonneg (t := ((n + 0 : ℕ) : ℝ)) (by push_cast; linarith)
            linarith
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK.le
      calc ∑ m ∈ range (n + 1 + j), intWeight B₀ m ≤ phiT n - phiT ((n + j : ℕ) : ℝ) :=
            int_step B₀ hB j
        _ ≤ phiT n := by
            have := phiT_nonneg (t := ((n + j : ℕ) : ℝ)) (by push_cast; linarith)
            linarith
  exact (hS K).trans hphi

end Elem

open Elem in

/- English proof (translation)
Introduce `f N B₀ hf hN hB`. Establish `hB16 : 16 ≤ B₀`. Establish `hf' : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hN' : (2 : ℝ) ≤ N` using `by exact_mod_cast hN`. Use the polynomial consequences of the given equalities and inequalities.

Use `set s : Set ℕ := {m | B₀ < m}`. Establish `hind : s.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ 2) = intWeight B₀`. Use function extensionality and compare the values at `m`. Distinguish the cases in `h : B₀ < m`. Simplify using `[s, Set.indicator_of_mem, h, intWeight]`.

Simplify using `[s, Set.indicator_of_notMem, h, intWeight]`. Establish `hsum : Summable (intWeight B₀)` using `summable_of_sum_range_le (intWeight_nonneg B₀) (int_partial_le B₀ hB16)`. Establish `hsub : Summable (fun m : s => Real.log m / (m : ℝ) ^ 2)`. Use `(summable_subtype_iff_indicator (f := fun m : ℕ => Real.log m / (m : ℝ) ^ 2) (s := s)).mpr (by rw [hind]; exact hsum)` as an intermediate fact. Conclude with `this`.

Use `⟨hsub, ?_⟩` and prove the remaining obligations. Establish `: ∑' m : s, Real.log m / (m : ℝ) ^ 2 ≤ 2 * (1 + Real.log B₀) / B₀`. Rewrite using `[tsum_subtype s (fun m : ℕ => Real.log m / (m : ℝ) ^ 2), hind]`. Conclude with `Real.tsum_le_of_sum_range_le (intWeight_nonneg B₀) (int_partial_le B₀ hB16)`. Conclude with `this`.
-/
theorem IntegerLogSquareTail.intersectionNumber_baseChange : IntegerLogSquareTail.Statement := by
  intro f N B₀ hf hN hB
  have hB16 : 16 ≤ B₀ := by
    have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  set s : Set ℕ := {m | B₀ < m}
  have hind : s.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ 2) = intWeight B₀ := by
    funext m
    by_cases h : B₀ < m
    · simp [s, Set.indicator_of_mem, h, intWeight]
    · simp [s, Set.indicator_of_notMem, h, intWeight]
  have hsum : Summable (intWeight B₀) :=
    summable_of_sum_range_le (intWeight_nonneg B₀) (int_partial_le B₀ hB16)
  have hsub : Summable (fun m : s => Real.log m / (m : ℝ) ^ 2) := by
    have := (summable_subtype_iff_indicator (f := fun m : ℕ => Real.log m / (m : ℝ) ^ 2)
      (s := s)).mpr (by rw [hind]; exact hsum)
    exact this
  refine ⟨hsub, ?_⟩
  have : ∑' m : s, Real.log m / (m : ℝ) ^ 2 ≤ 2 * (1 + Real.log B₀) / B₀ := by
    rw [tsum_subtype s (fun m : ℕ => Real.log m / (m : ℝ) ^ 2), hind]
    exact Real.tsum_le_of_sum_range_le (intWeight_nonneg B₀) (int_partial_le B₀ hB16)
  exact this

end

end RestTerms

end GroundTheory.Heights₂.Heights
