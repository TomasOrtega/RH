import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigenInputs
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open Finset

namespace PrimeLogSum

/- English proof (translation)
Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem term_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  calc Real.log p / ((p : ℝ) - 1) ≤ Real.log p / ((p : ℝ) / 2) :=
        div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity) (by linarith)
    _ = 2 * (Real.log p / p) := by ring

/- English proof (translation)
Establish `h1 : ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / (2 : ℝ) ^ k`. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Take `⟨hpp, hk⟩` from `hS p hp`. Apply `div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity)` to reduce the goal to its premises.

Use `Nat.pow_log_le_self 2 hpp.ne_zero` as an intermediate fact. Rewrite `this` using `[hk]`. Conclude with `this` after adjusting the coercions. Establish `h2 : ∑ p ∈ S, Real.log p ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ)`. Rewrite using `[Chebyshev.theta, Nat.floor_natCast]`.

Apply `sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `p hp`. Take `⟨hpp, hk⟩` from `hS p hp`. Use `Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p` as an intermediate fact. Rewrite `this` using `[hk]`.

Simplify using `only [mem_filter, mem_Ioc]`. Conclude with `⟨⟨hpp.pos, this.le⟩, hpp⟩`. Introduce `p _ _`. Conclude with `Real.log_natCast_nonneg p`. Establish `h3` using `Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (k + 1) : ℕ) : ℝ)) (by positivity)`.

Establish `hk : (0 : ℝ) < 2 ^ k` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts.
-/
theorem block_le (k : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ Nat.log 2 p = k) :
    ∑ p ∈ S, Real.log p / p ≤ 2 * Real.log 4 := by
  have h1 : ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / (2 : ℝ) ^ k := by
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp, hk⟩ := hS p hp
    apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity)
    have := Nat.pow_log_le_self 2 hpp.ne_zero
    rw [hk] at this
    exact_mod_cast this
  have h2 : ∑ p ∈ S, Real.log p ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) := by
    rw [Chebyshev.theta, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, hk⟩ := hS p hp
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
      rw [hk] at this
      simp only [mem_filter, mem_Ioc]
      exact ⟨⟨hpp.pos, this.le⟩, hpp⟩
    · intro p _ _
      exact Real.log_natCast_nonneg p
  have h3 := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (k + 1) : ℕ) : ℝ)) (by positivity)
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  calc ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / (2 : ℝ) ^ k := h1
    _ = (∑ p ∈ S, Real.log p) / (2 : ℝ) ^ k := by rw [sum_div]
    _ ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ k := by gcongr
    _ ≤ Real.log 4 * ((2 ^ (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ k := by gcongr
    _ = 2 * Real.log 4 := by
      push_cast
      rw [pow_succ]
      field_simp

/- English proof (translation)
Establish `h` using `Nat.pow_log_le_self 2 hN`. Establish `h' : (2 : ℝ) ^ Nat.log 2 N ≤ N` using `by exact_mod_cast h`. Use `Real.log_le_log (by positivity) h'` as an intermediate fact. Rewrite `this` using `[Real.log_pow]`. Then use the resulting hypothesis.
-/
theorem natLog_mul_log_two_le {N : ℕ} (hN : N ≠ 0) :
    (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h := Nat.pow_log_le_self 2 hN
  have h' : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow] at this

/- English proof (translation)
Establish `hmap : ∀ p ∈ S, Nat.log 2 p ∈ range (Nat.log 2 N + 1)`. Introduce `p hp`. Simplify using `only [mem_range]`. Conclude with `Nat.lt_succ_of_le (Nat.log_mono_right (hS p hp).2)`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmap]`.

Establish `hblocks : ∑ k ∈ range (Nat.log 2 N + 1), ∑ p ∈ S with Nat.log 2 p = k, Real.log p / p ≤ ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4`. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `k _`. Apply `block_le k` to reduce the goal to its premises. Introduce `p hp`.

Simplify using `only [mem_filter] at hp`. Conclude with `⟨(hS p hp.1).1, hp.2⟩`. Establish `hcount : ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4 = 2 * Real.log 4 * ((Nat.log 2 N : ℝ) + 1)`. Simplify using `[sum_const, card_range]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hlog4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hN' : (2 : ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `hl2 : Real.log 2 ≤ Real.log N` using `Real.log_le_log (by norm_num) hN'`. Establish `hnl` using `natLog_mul_log_two_le (N := N) (by omega)`. Establish `hl2pos : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem small_le {N : ℕ} (hN : 2 ≤ N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) :
    ∑ p ∈ S, Real.log p / p ≤ 8 * Real.log N := by
  have hmap : ∀ p ∈ S, Nat.log 2 p ∈ range (Nat.log 2 N + 1) := by
    intro p hp
    simp only [mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (hS p hp).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hblocks : ∑ k ∈ range (Nat.log 2 N + 1), ∑ p ∈ S with Nat.log 2 p = k, Real.log p / p
      ≤ ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4 := by
    apply sum_le_sum
    intro k _
    apply block_le k
    intro p hp
    simp only [mem_filter] at hp
    exact ⟨(hS p hp.1).1, hp.2⟩
  have hcount : ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4
      = 2 * Real.log 4 * ((Nat.log 2 N : ℝ) + 1) := by
    simp [sum_const, card_range]
    ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  have hnl := natLog_mul_log_two_le (N := N) (by omega)
  have hl2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc _ ≤ _ := hblocks
    _ = 2 * Real.log 4 * ((Nat.log 2 N : ℝ) + 1) := hcount
    _ = 4 * ((Nat.log 2 N : ℝ) * Real.log 2 + Real.log 2) := by rw [hlog4]; ring
    _ ≤ 4 * (Real.log N + Real.log N) := by gcongr
    _ ≤ 8 * Real.log N := by linarith

/- English proof (translation)
Establish `hB' : (2 : ℝ) ≤ B` using `by exact_mod_cast hB`. Establish `he : Real.exp 1 ≤ (B : ℝ) + 1`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : ∀ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1))`.

Introduce `p hp`. Establish `hBp : B + 1 ≤ p` using `hS p hp`. Establish `hBp' : (B : ℝ) + 1 ≤ p` using `by exact_mod_cast hBp`. Use `(term_le (by omega)).trans ?_` and prove the remaining obligations. Use `Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (he.trans hBp')) hBp'` as an intermediate fact.

Simplify using `only at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum` using `sum_le_sum hterm`. Rewrite `hsum` using `[sum_const, nsmul_eq_mul]`. Establish `hcard' : (S.card : ℝ) ≤ B` using `by exact_mod_cast hcard`.

Establish `hlogpos : 0 ≤ Real.log ((B : ℝ) + 1)` using `Real.log_nonneg (by linarith)`. Establish `hq : 0 ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1))` using `by positivity`. Establish `h1 : (S.card : ℝ) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1))) ≤ 2 * Real.log ((B : ℝ) + 1)`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.

Use `_ = 2 * Real.log ((B : ℝ) + 1) := by field_simp`. Establish `h2 : Real.log ((B : ℝ) + 1) ≤ 2 * Real.log B`. Establish `h` using `Real.log_le_log (by linarith : (0 : ℝ) < (B : ℝ) + 1) (show (B : ℝ) + 1 ≤ (B : ℝ) ^ 2 by nlinarith)`. Rewrite `h` using `[Real.log_pow]`. Move the coercions through the operations in `at h`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem large_le {B : ℕ} (hB : 2 ≤ B) (S : Finset ℕ) (hS : ∀ p ∈ S, B < p) (hcard : S.card ≤ B) :
    ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B := by
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have he : Real.exp 1 ≤ (B : ℝ) + 1 := by
    have := Real.exp_one_lt_d9
    linarith
  have hterm : ∀ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)) := by
    intro p hp
    have hBp : B + 1 ≤ p := hS p hp
    have hBp' : (B : ℝ) + 1 ≤ p := by exact_mod_cast hBp
    refine (term_le (by omega)).trans ?_
    have := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he)
      (Set.mem_Ici.mpr (he.trans hBp')) hBp'
    simp only at this
    linarith
  have hsum := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hsum
  have hcard' : (S.card : ℝ) ≤ B := by exact_mod_cast hcard
  have hlogpos : 0 ≤ Real.log ((B : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hq : 0 ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)) := by positivity
  have h1 : (S.card : ℝ) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)))
      ≤ 2 * Real.log ((B : ℝ) + 1) := by
    calc (S.card : ℝ) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)))
        ≤ ((B : ℝ) + 1) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1))) := by
          gcongr
          linarith
      _ = 2 * Real.log ((B : ℝ) + 1) := by field_simp
  have h2 : Real.log ((B : ℝ) + 1) ≤ 2 * Real.log B := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (B : ℝ) + 1)
      (show (B : ℝ) + 1 ≤ (B : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  linarith

/- English proof (translation)
Use `⟨20, fun B hB P hP hcard => ?_⟩` and prove the remaining obligations. Rewrite using `[← sum_filter_add_sum_filter_not P (fun p => p ≤ B)]`. Establish `hsmall : ∑ p ∈ P with p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 16 * Real.log B`. Combine the equalities or inequalities in the displayed calculation. Apply `sum_le_sum` to reduce the goal to its premises.

Introduce `p hp`. Simplify using `only [mem_filter] at hp`. Conclude with `term_le (hP p hp.1).two_le`. Use `_ = 2 * ∑ p ∈ P with p ≤ B, Real.log p / p := by rw [mul_sum]`. Use `_ ≤ 2 * (8 * Real.log B) := by gcongr`.

Apply `small_le hB` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [mem_filter] at hp`. Conclude with `⟨hP p hp.1, hp.2⟩`. Use `_ = 16 * Real.log B := by ring`.

Establish `hlarge : ∑ p ∈ P with ¬ p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B`. Apply `large_le hB` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [mem_filter] at hp`. Use linear arithmetic over natural numbers and integers.

Conclude with `(card_filter_le _ _).trans hcard`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem full : Statement := by
  refine ⟨20, fun B hB P hP hcard => ?_⟩
  rw [← sum_filter_add_sum_filter_not P (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ P with p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 16 * Real.log B := by
    calc ∑ p ∈ P with p ≤ B, Real.log p / ((p : ℝ) - 1)
        ≤ ∑ p ∈ P with p ≤ B, 2 * (Real.log p / p) := by
          apply sum_le_sum
          intro p hp
          simp only [mem_filter] at hp
          exact term_le (hP p hp.1).two_le
      _ = 2 * ∑ p ∈ P with p ≤ B, Real.log p / p := by rw [mul_sum]
      _ ≤ 2 * (8 * Real.log B) := by
          gcongr
          apply small_le hB
          intro p hp
          simp only [mem_filter] at hp
          exact ⟨hP p hp.1, hp.2⟩
      _ = 16 * Real.log B := by ring
  have hlarge : ∑ p ∈ P with ¬ p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B := by
    apply large_le hB
    · intro p hp
      simp only [mem_filter] at hp
      omega
    · exact (card_filter_le _ _).trans hcard
  linarith

end PrimeLogSum

end GroundTheory.Heights₂.Heights.NineStatements
