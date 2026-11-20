import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPrimesInvPredLeLoglogStatement

open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.SumBound

open Finset

/- English proof (translation)
Establish `h` using `primorial_le_4_pow M`. Unfold `primorial at h`. Establish `h' : (∏ p ∈ (range (M + 1)).filter Nat.Prime, (p:ℝ)) ≤ (4:ℝ) ^ M`. Rewrite using `[← Nat.cast_prod]`. Conclude with `h` after adjusting the coercions.

Establish `hpos : ∀ p ∈ (range (M + 1)).filter Nat.Prime, (0:ℝ) < (p:ℝ)`. Introduce `p hp`. Use `(mem_filter.1 hp).2.pos` as an intermediate fact. Check the signs of the components of the expression. Use `Real.log_le_log (Finset.prod_pos hpos) h'` as an intermediate fact.

Rewrite `this` using `[Real.log_prod (fun p hp => (hpos p hp).ne')]`. Simplify `this` using `[Real.log_pow]`.
-/
theorem sum_log_le (M : ℕ) :
    ∑ p ∈ (range (M + 1)).filter Nat.Prime, Real.log p ≤ M * Real.log 4 := by
  have h := primorial_le_4_pow M
  unfold primorial at h
  have h' : (∏ p ∈ (range (M + 1)).filter Nat.Prime, (p:ℝ)) ≤ (4:ℝ) ^ M := by
    rw [← Nat.cast_prod]
    exact_mod_cast h
  have hpos : ∀ p ∈ (range (M + 1)).filter Nat.Prime, (0:ℝ) < (p:ℝ) := by
    intro p hp
    have := (mem_filter.1 hp).2.pos
    positivity
  have := Real.log_le_log (Finset.prod_pos hpos) h'
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')] at this
  simpa [Real.log_pow] using this

/- English proof (translation)
Establish `hv` using `hvd p`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hp1 : (0:ℝ) < (p:ℝ) - 1` using `by linarith`. Unfold `eOf eSmall`. Use `split_ifs with h1 h2 h3 h4`.

Conclude with `le_rfl`. Check the signs of the components of the expression. Check the signs of the components of the expression. Establish `hM : (1:ℝ) ≤ M`. Establish `: 2 ≤ M` using `le_trans hp.two_le (not_lt.1 h1)`.

Conclude with `(show 1 ≤ M by omega)` after adjusting the coercions. Establish `hl : 0 ≤ Real.logb p M` using `Real.logb_nonneg (by linarith) hM`. Check the signs of the components of the expression. Check the signs of the components of the expression.
-/
theorem eOf_nonneg (F N k m : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (M : ℕ) (S₀ R : Finset ℕ) (hMb : 0 ≤ Mb) (hSm : 0 ≤ Sm)
    (hvd : ∀ q, 0 ≤ vd q) (p : ℕ) (hp : p.Prime) : 0 ≤ eOf F N k m Mb Sm vd M S₀ R p := by
  have hv := hvd p
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  unfold eOf eSmall
  split_ifs with h1 h2 h3 h4
  · exact le_rfl
  · positivity
  · positivity
  · have hM : (1:ℝ) ≤ M := by
      have : 2 ≤ M := le_trans hp.two_le (not_lt.1 h1)
      exact_mod_cast (show 1 ≤ M by omega)
    have hl : 0 ≤ Real.logb p M := Real.logb_nonneg (by linarith) hM
    positivity
  · positivity

/- English proof (translation)
Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hp1 : (0:ℝ) < (p:ℝ) - 1` using `by linarith`. Establish `hlp : 0 < Real.log p` using `Real.log_pos (by linarith)`. Establish `hlp1 : Real.log p ≤ (p:ℝ) - 1`. Use `Real.log_le_sub_one_of_pos (show (0:ℝ) < p by linarith); linarith` as an intermediate fact.

Establish `ht0 : 0 ≤ Real.log p / ((p:ℝ) - 1)` using `div_nonneg hlp.le hp1.le`. Establish `ht1 : Real.log p / ((p:ℝ) - 1) ≤ 1` using `(div_le_one hp1).2 hlp1`. Establish `hMr : (p:ℝ) ≤ M` using `by exact_mod_cast hpM`. Establish `hlpM : Real.log p ≤ Real.log M` using `Real.log_le_log (by linarith) hMr`. Establish `hF : (0:ℝ) ≤ F` using `Nat.cast_nonneg _`.

Establish `hm : (0:ℝ) ≤ m` using `Nat.cast_nonneg _`. Establish `hN : (0:ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hX : 0 ≤ (F:ℝ) * m * Mb` using `by positivity`. Establish `hA : 0 ≤ ((F:ℝ) * m * Mb + Sm) * large₂` using `by nlinarith`. Establish `hinv : 0 ≤ 1 / ((p:ℝ) - 1)` using `by positivity`.

Establish `hv` using `hvd p`. Establish `hI2 : 0 ≤ (if p ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) else 0)` using `by split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`. Apply the tactic sequence `have hIR : 0 ≤ (if p ∈ R then ((F:ℝ) * m * Mb + Sm) * large₂ else 0) := by split_ifs <;> linarith`.

Establish `hIk : 0 ≤ (if m * p < k then (F:ℝ) * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1)) + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂ else 0)` using `by split_ifs`. Establish `h1 : 0 ≤ (F:ℝ) * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1))` using `mul_nonneg (div_nonneg (mul_nonneg hX (by linarith)) (by norm_num)) hinv`. Establish `h2 : 0 ≤ 2 * (F:ℝ) * (m + 1) * (N : ℝ) ^ 2 * large₂` using `mul_nonneg (by positivity) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_rfl`.

Establish `hB : 0 ≤ (6 * (F:ℝ) * m * Mb + Sm) * (Real.log p / ((p : ℝ) - 1))` using `mul_nonneg (by positivity) ht0`. Establish `hXt : 0 ≤ (F:ℝ) * m * Mb * (Real.log p / ((p : ℝ) - 1))` using `mul_nonneg hX ht0`. Establish `hnM : ¬ M < p` using `by omega`. Unfold `eOf`. Rewrite using `[if_neg hnM]`.

Distinguish the cases in `h2 : p ∈ S₀`. Rewrite using `[if_pos h2, if_pos h2]`. Establish `e : ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) = ((F:ℝ) * m * (1 + vd p / 2) * Mb + Sm) * Real.log p + Sm * (vd p / 2 * Real.log p)` using `by ring`. Establish `e0 : 0 ≤ Sm * (vd p / 2 * Real.log p)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[if_neg h2]`. Distinguish the cases in `hR : p ∈ R`. Rewrite using `[if_pos hR]`. Simplify using `only [h2, hR, ↓reduceIte] at hI2 hIR ⊢`. Establish `e : ((F:ℝ) * N * Mb + Sm) / ((p:ℝ) - 1) * Real.log p = F * Mb * (N * Real.log p / ((p:ℝ) - 1)) + Sm * (Real.log p / ((p:ℝ) - 1))` using `by ring`.

Rewrite using `[e]`. Establish `f1 : (F:ℝ) * Mb * (N * Real.log p / ((p:ℝ) - 1)) ≤ F * Mb * (m * large₂)` using `mul_le_mul_of_nonneg_left (hRq p hR) (by positivity)`. Establish `f2 : Sm * (Real.log p / ((p:ℝ) - 1)) ≤ Sm * large₂` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[if_neg hR]`.

Simplify using `only [h2, hR, ↓reduceIte, add_zero, zero_add] at hI2 hIR ⊢`. Distinguish the cases in `hk : m * p < k`. Rewrite using `[if_pos hk, if_pos hk]`. Unfold `eSmall`. Establish `hlb : Real.logb p M * Real.log p = Real.log M`.

Rewrite using `[Real.logb, div_mul_cancel₀ _ hlp.ne']`. Establish `e : (((F:ℝ) * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p:ℝ) - 1) + F * (m + 1) * (N:ℝ) ^ 2 * (Real.logb p M + 1) + 1) * Real.log p = (4 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1)) + F * m * Mb / 2 * (Real.logb p M * Real.log p) * (1 / ((p:ℝ) - 1)) + F * (m + 1) * (N:ℝ) ^ 2 …` using `by ring`. Rewrite using `[e, hlb]`. Establish `g1 : (F:ℝ) * m * Mb / 2 * Real.log M * (1 / ((p:ℝ) - 1)) ≤ F * m * Mb * large₂ / 2 * (1 / ((p:ℝ) - 1))`. Establish `: (F:ℝ) * m * Mb / 2 * Real.log M ≤ F * m * Mb * large₂ / 2` using `by nlinarith`.

Conclude with `mul_le_mul_of_nonneg_right this hinv`. Establish `hQ : 0 ≤ (F:ℝ) * (m + 1) * (N:ℝ) ^ 2` using `by positivity`. Establish `g2 : (F:ℝ) * (m + 1) * (N:ℝ) ^ 2 * (Real.log M + Real.log p) ≤ F * (m + 1) * (N:ℝ) ^ 2 * (2 * large₂)` using `mul_le_mul_of_nonneg_left (by linarith) hQ`. Establish `g0 : (4 * (F:ℝ) * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1)) ≤ (6 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1))` using `mul_le_mul_of_nonneg_right (by linarith) ht0`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[if_neg hk, if_neg hk]`. Establish `e : ((6 * (F:ℝ) * m * Mb + Sm) / ((p:ℝ) - 1) + 1) * Real.log p = (6 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1)) + Real.log p` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem point_le (F N k m M : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (large₂ : ℝ) (S₀ R : Finset ℕ) (hMb : 0 ≤ Mb) (hSm : 0 ≤ Sm)
    (hvd : ∀ q, 0 ≤ vd q) (hLg : 1 ≤ large₂) (hLM : Real.log M ≤ large₂)
    (hRq : ∀ q ∈ R, N * Real.log q / ((q : ℝ) - 1) ≤ m * large₂) (p : ℕ) (hp : p.Prime) (hpM : p ≤ M) :
    eOf F N k m Mb Sm vd M S₀ R p * Real.log p ≤
      (if p ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) else 0) + (if p ∈ R then (F * m * Mb + Sm) * large₂ else 0)
      + (6 * F * m * Mb + Sm) * (Real.log p / ((p : ℝ) - 1)) + Real.log p
      + (if m * p < k then F * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1)) + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂
          else 0) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlp1 : Real.log p ≤ (p:ℝ) - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < p by linarith); linarith
  have ht0 : 0 ≤ Real.log p / ((p:ℝ) - 1) := div_nonneg hlp.le hp1.le
  have ht1 : Real.log p / ((p:ℝ) - 1) ≤ 1 := (div_le_one hp1).2 hlp1
  have hMr : (p:ℝ) ≤ M := by exact_mod_cast hpM
  have hlpM : Real.log p ≤ Real.log M := Real.log_le_log (by linarith) hMr
  have hF : (0:ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hX : 0 ≤ (F:ℝ) * m * Mb := by positivity
  have hA : 0 ≤ ((F:ℝ) * m * Mb + Sm) * large₂ := by nlinarith
  have hinv : 0 ≤ 1 / ((p:ℝ) - 1) := by positivity
  have hv := hvd p
  have hI2 : 0 ≤ (if p ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have hIR : 0 ≤ (if p ∈ R then ((F:ℝ) * m * Mb + Sm) * large₂ else 0) := by split_ifs <;> linarith
  have hIk : 0 ≤ (if m * p < k then (F:ℝ) * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1))
      + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂ else 0) := by
    split_ifs
    · have h1 : 0 ≤ (F:ℝ) * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1)) :=
        mul_nonneg (div_nonneg (mul_nonneg hX (by linarith)) (by norm_num)) hinv
      have h2 : 0 ≤ 2 * (F:ℝ) * (m + 1) * (N : ℝ) ^ 2 * large₂ :=
        mul_nonneg (by positivity) (by linarith)
      linarith
    · exact le_rfl
  have hB : 0 ≤ (6 * (F:ℝ) * m * Mb + Sm) * (Real.log p / ((p : ℝ) - 1)) :=
    mul_nonneg (by positivity) ht0
  have hXt : 0 ≤ (F:ℝ) * m * Mb * (Real.log p / ((p : ℝ) - 1)) := mul_nonneg hX ht0
  have hnM : ¬ M < p := by omega
  unfold eOf
  rw [if_neg hnM]
  by_cases h2 : p ∈ S₀
  · rw [if_pos h2, if_pos h2]
    have e : ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) = ((F:ℝ) * m * (1 + vd p / 2) * Mb + Sm) * Real.log p + Sm * (vd p / 2 * Real.log p) := by ring
    have e0 : 0 ≤ Sm * (vd p / 2 * Real.log p) := by positivity
    linarith
  · rw [if_neg h2]
    by_cases hR : p ∈ R
    · rw [if_pos hR]
      simp only [h2, hR, ↓reduceIte] at hI2 hIR ⊢
      have e : ((F:ℝ) * N * Mb + Sm) / ((p:ℝ) - 1) * Real.log p
          = F * Mb * (N * Real.log p / ((p:ℝ) - 1)) + Sm * (Real.log p / ((p:ℝ) - 1)) := by ring
      rw [e]
      have f1 : (F:ℝ) * Mb * (N * Real.log p / ((p:ℝ) - 1)) ≤ F * Mb * (m * large₂) :=
        mul_le_mul_of_nonneg_left (hRq p hR) (by positivity)
      have f2 : Sm * (Real.log p / ((p:ℝ) - 1)) ≤ Sm * large₂ := by nlinarith
      nlinarith
    · rw [if_neg hR]
      simp only [h2, hR, ↓reduceIte, add_zero, zero_add] at hI2 hIR ⊢
      by_cases hk : m * p < k
      · rw [if_pos hk, if_pos hk]
        unfold eSmall
        have hlb : Real.logb p M * Real.log p = Real.log M := by
          rw [Real.logb, div_mul_cancel₀ _ hlp.ne']
        have e : (((F:ℝ) * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p:ℝ) - 1)
            + F * (m + 1) * (N:ℝ) ^ 2 * (Real.logb p M + 1) + 1) * Real.log p
            = (4 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1))
              + F * m * Mb / 2 * (Real.logb p M * Real.log p) * (1 / ((p:ℝ) - 1))
              + F * (m + 1) * (N:ℝ) ^ 2 * (Real.logb p M * Real.log p + Real.log p) + Real.log p := by ring
        rw [e, hlb]
        have g1 : (F:ℝ) * m * Mb / 2 * Real.log M * (1 / ((p:ℝ) - 1))
            ≤ F * m * Mb * large₂ / 2 * (1 / ((p:ℝ) - 1)) := by
          have : (F:ℝ) * m * Mb / 2 * Real.log M ≤ F * m * Mb * large₂ / 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this hinv
        have hQ : 0 ≤ (F:ℝ) * (m + 1) * (N:ℝ) ^ 2 := by positivity
        have g2 : (F:ℝ) * (m + 1) * (N:ℝ) ^ 2 * (Real.log M + Real.log p)
            ≤ F * (m + 1) * (N:ℝ) ^ 2 * (2 * large₂) :=
          mul_le_mul_of_nonneg_left (by linarith) hQ
        have g0 : (4 * (F:ℝ) * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1))
            ≤ (6 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) ht0
        linarith
      · rw [if_neg hk, if_neg hk]
        have e : ((6 * (F:ℝ) * m * Mb + Sm) / ((p:ℝ) - 1) + 1) * Real.log p
            = (6 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1)) + Real.log p := by ring
        rw [e]
        linarith

end GlobalTheory.SumBound

namespace GlobalTheory.SumBound

open Finset

/- English proof (translation)
Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`.
-/
theorem sum_ite_const (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (c : ℝ) :
    ∑ q ∈ s, (if P q then c else 0) = (s.filter P).card * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

/- English proof (translation)
Introduce `F N k m M Mb Sm vd large₂ ll S₀ R hMb hSm hvd hNk hmk hm1 hLg hll hLM hLN hvdL hllk hRc hRq`. Use `set S := (Finset.range (M + 1)).filter Nat.Prime with hS`. Use `⟨fun q hq => (mem_filter.1 hq).2, fun q => ?_, fun q hq => ?_, ?_⟩` and prove the remaining obligations. Use `beta_reduce split_ifs with h`. Conclude with `eOf_nonneg F N k m Mb Sm vd M S₀ R hMb hSm hvd q h`.

Conclude with `le_rfl`. Use `beta_reduce split_ifs with h`. Establish `hqM : M < q`. Assume the negation of the conclusion as `hc`. Conclude with `hq (mem_filter.2 ⟨mem_range.2 (by omega), h⟩)`.

Unfold `eOf`. Rewrite using `[if_pos hqM]`. Both sides reduce to the same expression. Establish `hF : (0:ℝ) ≤ F` using `Nat.cast_nonneg _`. Establish `hm : (0:ℝ) ≤ m` using `Nat.cast_nonneg _`.

Establish `hN : (0:ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hMn : (0:ℝ) ≤ M` using `Nat.cast_nonneg _`. Establish `hX : 0 ≤ (F:ℝ) * m * Mb` using `by positivity`. Establish `hA : 0 ≤ ((F:ℝ) * m * Mb + Sm) * large₂` using `by nlinarith`. Use `set A := ((F:ℝ) * m * Mb + Sm) * large₂ with hAdef`.

Use `set K := S.filter (fun q => m * q < k) with hK`. Establish `step1 : ∑ q ∈ S, (if q.Prime then eOf F N k m Mb Sm vd M S₀ R q else 0) * Real.log q ≤ ∑ q ∈ S, ((if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0) + (if q ∈ R then A else 0) + (6 * F * m * Mb + Sm) * (Real.log q / ((q : ℝ) - 1)) + Real.log q + (if m * …`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `q hq`. Establish `hqp` using `(mem_filter.1 hq).2`.

Establish `hqM : q ≤ M` using `by have := mem_range.1 (mem_filter.1 hq).1; omega`. Rewrite using `[if_pos hqp]`. Conclude with `point_le F N k m M Mb Sm vd large₂ S₀ R hMb hSm hvd hLg hLM hRq q hqp hqM`. Simplify using `only [Finset.sum_add_distrib] at step1`. Establish `t4 : ∑ q ∈ S, (if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0) ≤ 3 / 2 * A`.

Rewrite using `[← Finset.sum_filter, ← Finset.mul_sum]`. Establish `h1 : ∑ q ∈ S.filter (fun q => q ∈ S₀), (1 + vd q / 2) * Real.log q ≤ ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q` using `Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.1 hx).2) fun q _ _ => mul_nonneg (by have := hvd q; positivity) (Real.log_natCast_nonneg q)`. Establish `h2` using `mul_le_mul_of_nonneg_left (h1.trans hvdL) (show 0 ≤ (F:ℝ) * m * Mb + Sm by positivity)`. Rewrite using `[hAdef]`. Combine the linear equalities and inequalities to obtain the conclusion.

Generalize the expression as in `(∑ q ∈ S, (if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0)) = W₀ at step1 t4`. Rewrite `step1` using `[sum_ite_const, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]`. Establish `cR : ((S.filter (fun q => q ∈ R)).card : ℝ) ≤ 2`. Establish `: (S.filter (fun q => q ∈ R)).card ≤ R.card` using `Finset.card_le_card (fun x hx => (mem_filter.1 hx).2)`. Conclude with `this.trans hRc` after adjusting the coercions.

Establish `hmert : ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) ≤ Real.log M + 2.2` using `GlobalTheory.PrimeLogSum.sum_log_div_pred_le M`. Establish `hlog4 : Real.log 4 ≤ 3`. Use `Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith` as an intermediate fact. Establish `hth : ∑ q ∈ S, Real.log q ≤ 3 * M`. Use `sum_log_le M` as an intermediate fact.

Establish `h2 : (M:ℝ) * Real.log 4 ≤ M * 3` using `mul_le_mul_of_nonneg_left hlog4 hMn`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKS : ∀ q ∈ K, q.Prime ∧ m * q < k` using `fun q hq => ⟨(mem_filter.1 (mem_filter.1 hq).1).2, (mem_filter.1 hq).2⟩`. Establish `hrec : ∑ q ∈ K, 1 / ((q : ℝ) - 1) ≤ 13 * ll`. Distinguish the cases in `hk3 : 3 ≤ k`.

Establish `sub : K ⊆ (Finset.range (k + 1)).filter Nat.Prime`. Introduce `q hq`. Take `⟨hp, hqk⟩` from `hKS q hq`. Use `mem_filter.2 ⟨mem_range.2 ?_, hp⟩` and prove the remaining obligations. Establish `: q ≤ m * q` using `Nat.le_mul_of_pos_left q (by omega)`.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => 1 / ((q : ℝ) - 1)) sub (fun q hq _ => by`. Establish `: (2:ℝ) ≤ q` using `by exact_mod_cast (mem_filter.1 hq).2.two_le`. Establish `: (0:ℝ) < (q:ℝ) - 1` using `by linarith`. Use the proof step `positivity)`.

Establish `h2` using `GlobalTheory.T.sum_primes_inv_pred_le_loglog k hk3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: K = ∅`. Apply `Finset.eq_empty_of_forall_notMem` to reduce the goal to its premises. Introduce `q hq`.

Take `⟨hp, hqk⟩` from `hKS q hq`. Establish `: 2 ≤ m * q` using `le_trans hp.two_le (Nat.le_mul_of_pos_left q (by omega))`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Finset.sum_empty]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcard : (K.card : ℝ) * ((m:ℝ) + 1) ≤ 2 * N`. Establish `sub : K ⊆ Finset.Icc 1 ((k - 1) / m)`. Introduce `q hq`. Take `⟨hp, hqk⟩` from `hKS q hq`. Use `Finset.mem_Icc.2 ⟨hp.one_lt.le, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.le_div_iff_mul_le (by omega)]`. Rewrite using `[Nat.mul_comm]`. Use linear arithmetic over natural numbers and integers. Establish `h1 : K.card ≤ (k - 1) / m`. Use `Finset.card_le_card sub` as an intermediate fact.

Simplify using `using this`. Establish `h2 : K.card * m ≤ k - 1` using `le_trans (Nat.mul_le_mul_right m h1) (Nat.div_mul_le_self _ _)`. Establish `h3 : K.card ≤ K.card * m` using `Nat.le_mul_of_pos_right _ (by omega)`. Establish `h4 : K.card * (m + 1) ≤ 2 * N` using `by rw [Nat.mul_succ]; omega`. Conclude with `h4` after adjusting the coercions.

Establish `hLg0 : (0:ℝ) ≤ large₂` using `by linarith`. Establish `hll0 : (0:ℝ) ≤ ll` using `by linarith`. Establish `t1 : (6 * (F:ℝ) * m * Mb + Sm) * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) ≤ (6 * (F:ℝ) * m * Mb + Sm) * (3.2 * large₂)` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Establish `t2 : (F:ℝ) * m * Mb * large₂ / 2 * ∑ q ∈ K, 1 / ((q : ℝ) - 1) ≤ (F:ℝ) * m * Mb * large₂ / 2 * (13 * ll)` using `mul_le_mul_of_nonneg_left hrec (by positivity)`. Establish `t3 : (K.card : ℝ) * (2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂) ≤ 2 * F * (N:ℝ) ^ 2 * large₂ * (2 * N)`.

Establish `e : (K.card : ℝ) * (2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂) = 2 * F * (N:ℝ) ^ 2 * large₂ * ((K.card : ℝ) * ((m:ℝ) + 1))` using `by ring`. Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_left hcard (by positivity)`. Establish `t5 : ((S.filter (fun q => q ∈ R)).card : ℝ) * A ≤ 2 * A` using `mul_le_mul_of_nonneg_right cR hA`. Establish `t6 : A ≤ A * ll` using `le_mul_of_one_le_right hA hll`.

Establish `hSL : 0 ≤ Sm * large₂` using `mul_nonneg hSm hLg0`. Establish `t7 : (F:ℝ) * m * Mb * large₂ ≤ A` using `by rw [hAdef]; linarith`. Establish `t8 : (F:ℝ) * m * Mb * large₂ * ll ≤ A * ll` using `mul_le_mul_of_nonneg_right t7 hll0`. Establish `t9 : (6 * (F:ℝ) * m * Mb + Sm) * (3.2 * large₂) ≤ 96 / 5 * A` using `by rw [hAdef]; norm_num; linarith`. Establish `t10 : 0 ≤ (F:ℝ) * (N:ℝ) ^ 3 * large₂` using `by positivity`.

Use `clear_value A`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem primeSum_eOf : ∀ (F N k m M : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (large₂ ll : ℝ) (S₀ R : Finset ℕ), 0 ≤ Mb → 0 ≤ Sm → (∀ q, 0 ≤ vd q) →
    N + 1 = k + m → m ≤ k → 1 ≤ m → 1 ≤ large₂ → 1 ≤ ll → Real.log M ≤ large₂ → Real.log N ≤ large₂ → ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q ≤ 3 / 2 * large₂ →
    Real.log (Real.log k) ≤ ll → R.card ≤ 2 → (∀ q ∈ R, N * Real.log q / ((q : ℝ) - 1) ≤ m * large₂) →
    PrimeSum ((Finset.range (M + 1)).filter Nat.Prime)
      (fun p => if p.Prime then eOf F N k m Mb Sm vd M S₀ R p else 0)
      (40 * ((F * m * Mb + Sm) * large₂ * ll + F * (N : ℝ) ^ 3 * large₂ + M)) := by
  intro F N k m M Mb Sm vd large₂ ll S₀ R hMb hSm hvd hNk hmk hm1 hLg hll hLM hLN hvdL hllk hRc hRq
  set S := (Finset.range (M + 1)).filter Nat.Prime with hS
  refine ⟨fun q hq => (mem_filter.1 hq).2, fun q => ?_, fun q hq => ?_, ?_⟩
  · beta_reduce
    split_ifs with h
    · exact eOf_nonneg F N k m Mb Sm vd M S₀ R hMb hSm hvd q h
    · exact le_rfl
  · beta_reduce
    split_ifs with h
    · have hqM : M < q := by
        by_contra hc
        exact hq (mem_filter.2 ⟨mem_range.2 (by omega), h⟩)
      unfold eOf; rw [if_pos hqM]
    · rfl

  have hF : (0:ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hMn : (0:ℝ) ≤ M := Nat.cast_nonneg _
  have hX : 0 ≤ (F:ℝ) * m * Mb := by positivity
  have hA : 0 ≤ ((F:ℝ) * m * Mb + Sm) * large₂ := by nlinarith
  set A := ((F:ℝ) * m * Mb + Sm) * large₂ with hAdef
  set K := S.filter (fun q => m * q < k) with hK
  have step1 : ∑ q ∈ S, (if q.Prime then eOf F N k m Mb Sm vd M S₀ R q else 0) * Real.log q ≤
      ∑ q ∈ S, ((if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0) + (if q ∈ R then A else 0)
      + (6 * F * m * Mb + Sm) * (Real.log q / ((q : ℝ) - 1)) + Real.log q
      + (if m * q < k then F * m * Mb * large₂ / 2 * (1 / ((q : ℝ) - 1)) + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂
          else 0)) := by
    apply Finset.sum_le_sum
    intro q hq
    have hqp := (mem_filter.1 hq).2
    have hqM : q ≤ M := by have := mem_range.1 (mem_filter.1 hq).1; omega
    rw [if_pos hqp]
    exact point_le F N k m M Mb Sm vd large₂ S₀ R hMb hSm hvd hLg hLM hRq q hqp hqM
  simp only [Finset.sum_add_distrib] at step1
  have t4 : ∑ q ∈ S, (if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0) ≤ 3 / 2 * A := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have h1 : ∑ q ∈ S.filter (fun q => q ∈ S₀), (1 + vd q / 2) * Real.log q ≤ ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.1 hx).2) fun q _ _ =>
        mul_nonneg (by have := hvd q; positivity) (Real.log_natCast_nonneg q)
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hvdL) (show 0 ≤ (F:ℝ) * m * Mb + Sm by positivity)
    rw [hAdef]; linarith
  generalize (∑ q ∈ S, (if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0)) = W₀ at step1 t4
  rw [sum_ite_const, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at step1

  have cR : ((S.filter (fun q => q ∈ R)).card : ℝ) ≤ 2 := by
    have : (S.filter (fun q => q ∈ R)).card ≤ R.card :=
      Finset.card_le_card (fun x hx => (mem_filter.1 hx).2)
    exact_mod_cast this.trans hRc
  have hmert : ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) ≤ Real.log M + 2.2 :=
    GlobalTheory.PrimeLogSum.sum_log_div_pred_le M
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  have hth : ∑ q ∈ S, Real.log q ≤ 3 * M := by
    have := sum_log_le M
    have h2 : (M:ℝ) * Real.log 4 ≤ M * 3 := mul_le_mul_of_nonneg_left hlog4 hMn
    linarith
  have hKS : ∀ q ∈ K, q.Prime ∧ m * q < k := fun q hq =>
    ⟨(mem_filter.1 (mem_filter.1 hq).1).2, (mem_filter.1 hq).2⟩
  have hrec : ∑ q ∈ K, 1 / ((q : ℝ) - 1) ≤ 13 * ll := by
    by_cases hk3 : 3 ≤ k
    · have sub : K ⊆ (Finset.range (k + 1)).filter Nat.Prime := by
        intro q hq
        obtain ⟨hp, hqk⟩ := hKS q hq
        refine mem_filter.2 ⟨mem_range.2 ?_, hp⟩
        have : q ≤ m * q := Nat.le_mul_of_pos_left q (by omega)
        omega
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => 1 / ((q : ℝ) - 1)) sub (fun q hq _ => by
        have : (2:ℝ) ≤ q := by exact_mod_cast (mem_filter.1 hq).2.two_le
        have : (0:ℝ) < (q:ℝ) - 1 := by linarith
        positivity)
      have h2 := GlobalTheory.T.sum_primes_inv_pred_le_loglog k hk3
      linarith
    · have : K = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro q hq
        obtain ⟨hp, hqk⟩ := hKS q hq
        have : 2 ≤ m * q := le_trans hp.two_le (Nat.le_mul_of_pos_left q (by omega))
        omega
      rw [this, Finset.sum_empty]; linarith
  have hcard : (K.card : ℝ) * ((m:ℝ) + 1) ≤ 2 * N := by
    have sub : K ⊆ Finset.Icc 1 ((k - 1) / m) := by
      intro q hq
      obtain ⟨hp, hqk⟩ := hKS q hq
      refine Finset.mem_Icc.2 ⟨hp.one_lt.le, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [Nat.mul_comm]; omega
    have h1 : K.card ≤ (k - 1) / m := by
      have := Finset.card_le_card sub
      simpa using this
    have h2 : K.card * m ≤ k - 1 := le_trans (Nat.mul_le_mul_right m h1) (Nat.div_mul_le_self _ _)
    have h3 : K.card ≤ K.card * m := Nat.le_mul_of_pos_right _ (by omega)
    have h4 : K.card * (m + 1) ≤ 2 * N := by rw [Nat.mul_succ]; omega
    exact_mod_cast h4

  have hLg0 : (0:ℝ) ≤ large₂ := by linarith
  have hll0 : (0:ℝ) ≤ ll := by linarith
  have t1 : (6 * (F:ℝ) * m * Mb + Sm) * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1)
      ≤ (6 * (F:ℝ) * m * Mb + Sm) * (3.2 * large₂) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t2 : (F:ℝ) * m * Mb * large₂ / 2 * ∑ q ∈ K, 1 / ((q : ℝ) - 1) ≤ (F:ℝ) * m * Mb * large₂ / 2 * (13 * ll) :=
    mul_le_mul_of_nonneg_left hrec (by positivity)
  have t3 : (K.card : ℝ) * (2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂) ≤ 2 * F * (N:ℝ) ^ 2 * large₂ * (2 * N) := by
    have e : (K.card : ℝ) * (2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂)
        = 2 * F * (N:ℝ) ^ 2 * large₂ * ((K.card : ℝ) * ((m:ℝ) + 1)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hcard (by positivity)
  have t5 : ((S.filter (fun q => q ∈ R)).card : ℝ) * A ≤ 2 * A := mul_le_mul_of_nonneg_right cR hA
  have t6 : A ≤ A * ll := le_mul_of_one_le_right hA hll
  have hSL : 0 ≤ Sm * large₂ := mul_nonneg hSm hLg0
  have t7 : (F:ℝ) * m * Mb * large₂ ≤ A := by rw [hAdef]; linarith
  have t8 : (F:ℝ) * m * Mb * large₂ * ll ≤ A * ll := mul_le_mul_of_nonneg_right t7 hll0
  have t9 : (6 * (F:ℝ) * m * Mb + Sm) * (3.2 * large₂) ≤ 96 / 5 * A := by rw [hAdef]; norm_num; linarith
  have t10 : 0 ≤ (F:ℝ) * (N:ℝ) ^ 3 * large₂ := by positivity
  clear_value A
  linarith

end GlobalTheory.SumBound
