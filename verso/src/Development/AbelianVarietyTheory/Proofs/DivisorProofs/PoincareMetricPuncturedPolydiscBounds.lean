import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section
namespace GlobalTheory.PoincareBounds

def pdiag {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) : ℝ :=
  if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * tlog (z k) ^ 2)) else 1 / 2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem poincareGram_eq {n : ℕ} (a : ℕ) (z : Fin n → ℂ) :
    poincareGram a z = diagonal fun k => ((pdiag a z k : ℝ) : ℂ) := rfl

/- English proof (translation)
Apply the tactic sequence `unfold pdiag; split_ifs <;> positivity`.
-/
theorem pdiag_nonneg {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) : 0 ≤ pdiag a z k := by
  unfold pdiag; split_ifs <;> positivity

/- English proof (translation)
Establish `hP : (diagonal fun k => ((d k : ℝ) : ℂ)).PosSemidef`. Rewrite using `[posSemidef_diagonal_iff]`. Introduce `k`. Conclude with `hd k` after adjusting the coercions. Rewrite using `[gnorm_sq hP, form_eq_sum]`.

Simplify using `only [diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, re_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (ξ k), mul_assoc, mul_conj, ← ofReal_mul, ofReal_re, normSq_eq_norm_sq]`.
-/
theorem gnorm_diag_sq {n : ℕ} (d : Fin n → ℝ) (hd : ∀ k, 0 ≤ d k) (ξ : Fin n → ℂ) :
    gnorm (diagonal fun k => ((d k : ℝ) : ℂ)) ξ ^ 2 = ∑ k, d k * ‖ξ k‖ ^ 2 := by
  have hP : (diagonal fun k => ((d k : ℝ) : ℂ)).PosSemidef := by
    rw [posSemidef_diagonal_iff]; intro k; exact_mod_cast hd k
  rw [gnorm_sq hP, form_eq_sum]
  simp only [diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm (ξ k), mul_assoc, mul_conj, ← ofReal_mul, ofReal_re, normSq_eq_norm_sq]

/- English proof (translation)
Establish `hx : 0 < ‖w‖` using `norm_pos_iff.2 h0`. Use `⟨mul_pos hx (tlog_pos h0 h1), ?_⟩` and prove the remaining obligations. Establish `hl` using `Real.abs_log_mul_self_lt ‖w‖ hx h1.le`. Establish `hpi : 1 < 2 * Real.pi` using `by linarith [Real.pi_gt_three]`. Establish `e : ‖w‖ * tlog w = -(Real.log ‖w‖ * ‖w‖) / (2 * Real.pi)`.

Unfold `tlog`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, div_lt_one (by linarith)]`. Use `neg_le_abs (Real.log ‖w‖ * ‖w‖)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_mul_tlog_lt {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) :
    0 < ‖w‖ * tlog w ∧ ‖w‖ * tlog w < 1 := by
  have hx : 0 < ‖w‖ := norm_pos_iff.2 h0
  refine ⟨mul_pos hx (tlog_pos h0 h1), ?_⟩
  have hl := Real.abs_log_mul_self_lt ‖w‖ hx h1.le
  have hpi : 1 < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have e : ‖w‖ * tlog w = -(Real.log ‖w‖ * ‖w‖) / (2 * Real.pi) := by
    unfold tlog; ring
  rw [e, div_lt_one (by linarith)]
  have := neg_le_abs (Real.log ‖w‖ * ‖w‖)
  linarith

/- English proof (translation)
Unfold `pdiag`. Use `split_ifs with hk`. Establish `h0 : z k ≠ 0` using `hz.2 ⟨k, hk⟩`. Take `⟨hp, hl⟩` from `norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)`. Establish `hs : ‖z k‖ ^ 2 * tlog (z k) ^ 2 = (‖z k‖ * tlog (z k)) ^ 2` using `by ring`.

Rewrite using `[hs]`. Establish `h2 : 0 < (‖z k‖ * tlog (z k)) ^ 2` using `by positivity`. Establish `h3 : (‖z k‖ * tlog (z k)) ^ 2 < 1` using `by nlinarith`. Rewrite using `[div_le_div_iff₀ (by norm_num) (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `le_rfl`.
-/
theorem half_le_pdiag {n a : ℕ} (ha : a ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1) {z : Fin n → ℂ}
    (hz : z ∈ punctured ha ρ) (k : Fin n) : 1 / 2 ≤ pdiag a z k := by
  unfold pdiag
  split_ifs with hk
  · have h0 : z k ≠ 0 := hz.2 ⟨k, hk⟩
    obtain ⟨hp, hl⟩ := norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)
    have hs : ‖z k‖ ^ 2 * tlog (z k) ^ 2 = (‖z k‖ * tlog (z k)) ^ 2 := by ring
    rw [hs]
    have h2 : 0 < (‖z k‖ * tlog (z k)) ^ 2 := by positivity
    have h3 : (‖z k‖ * tlog (z k)) ^ 2 < 1 := by nlinarith
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  · exact le_rfl

/- English proof (translation)
Rewrite using `[poincareGram_eq, gnorm_diag_sq _ (pdiag_nonneg a z)]`. Conclude with `Finset.single_le_sum (f := fun k => pdiag a z k * ‖ξ k‖ ^ 2) (fun j _ => mul_nonneg (pdiag_nonneg a z j) (by positivity)) (Finset.mem_univ k)`.
-/
theorem pdiag_term_le {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (ξ : Fin n → ℂ) (k : Fin n) :
    pdiag a z k * ‖ξ k‖ ^ 2 ≤ gnorm (poincareGram a z) ξ ^ 2 := by
  rw [poincareGram_eq, gnorm_diag_sq _ (pdiag_nonneg a z)]
  exact Finset.single_le_sum (f := fun k => pdiag a z k * ‖ξ k‖ ^ 2)
    (fun j _ => mul_nonneg (pdiag_nonneg a z j) (by positivity)) (Finset.mem_univ k)

/- English proof (translation)
Introduce `n a ha ρ hρ z hz`. Use `⟨?_, fun ξ => ⟨fun k => ?_, fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[poincareGram_eq, posSemidef_diagonal_iff]`. Introduce `k`. Conclude with `pdiag_nonneg a z k` after adjusting the coercions.

Establish `h1` using `pdiag_term_le a z ξ k`. Establish `h2` using `half_le_pdiag ha hρ hz k`. Establish `hG` using `gnorm_nonneg (poincareGram a z) ξ`. Establish `hx` using `norm_nonneg (ξ k)`. Establish `h3 : ‖ξ k‖ ^ 2 ≤ 2 * gnorm (poincareGram a z) ξ ^ 2` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Use `set k := Fin.castLE ha i with hkdef`. Establish `hk : k.val < a` using `i.2`. Establish `h0 : z k ≠ 0` using `hz.2 i`. Take `⟨hp, -⟩` from `norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)`.

Establish `h1` using `pdiag_term_le a z ξ k`. Establish `hd : pdiag a z k = 1 / (2 * (‖z k‖ * tlog (z k)) ^ 2)`. Unfold `pdiag`. Rewrite using `[if_pos hk]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[hd]`. Use `set s := ‖z k‖ * tlog (z k)`. Use `set G := gnorm (poincareGram a z) ξ`. Establish `hG : 0 ≤ G` using `gnorm_nonneg _ _`. Establish `hx` using `norm_nonneg (ξ k)`.

Establish `h3 : ‖ξ k‖ ^ 2 ≤ 2 * s ^ 2 * G ^ 2`. Establish `hs2 : 0 < 2 * s ^ 2` using `by positivity`. Rewrite `h1` using `[div_mul_eq_mul_div, one_mul, div_le_iff₀ hs2]`. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[mul_nonneg hp.le hG]`.
-/
theorem poincare_bounds : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 → ∀ z ∈ punctured ha ρ,
    (poincareGram a z).PosSemidef ∧ ∀ ξ : Fin n → ℂ, (∀ k, ‖ξ k‖ ≤ 2 * gnorm (poincareGram a z) ξ) ∧
      ∀ i : Fin a, ‖ξ (Fin.castLE ha i)‖ ≤
        2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) * gnorm (poincareGram a z) ξ := by
  intro n a ha ρ hρ z hz
  refine ⟨?_, fun ξ => ⟨fun k => ?_, fun i => ?_⟩⟩
  · rw [poincareGram_eq, posSemidef_diagonal_iff]
    intro k; exact_mod_cast pdiag_nonneg a z k
  · have h1 := pdiag_term_le a z ξ k
    have h2 := half_le_pdiag ha hρ hz k
    have hG := gnorm_nonneg (poincareGram a z) ξ
    have hx := norm_nonneg (ξ k)
    have h3 : ‖ξ k‖ ^ 2 ≤ 2 * gnorm (poincareGram a z) ξ ^ 2 := by nlinarith
    nlinarith
  · set k := Fin.castLE ha i with hkdef
    have hk : k.val < a := i.2
    have h0 : z k ≠ 0 := hz.2 i
    obtain ⟨hp, -⟩ := norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)
    have h1 := pdiag_term_le a z ξ k
    have hd : pdiag a z k = 1 / (2 * (‖z k‖ * tlog (z k)) ^ 2) := by
      unfold pdiag; rw [if_pos hk]; ring
    rw [hd] at h1
    set s := ‖z k‖ * tlog (z k)
    set G := gnorm (poincareGram a z) ξ
    have hG : 0 ≤ G := gnorm_nonneg _ _
    have hx := norm_nonneg (ξ k)
    have h3 : ‖ξ k‖ ^ 2 ≤ 2 * s ^ 2 * G ^ 2 := by
      have hs2 : 0 < 2 * s ^ 2 := by positivity
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs2] at h1
      linarith
    nlinarith [mul_nonneg hp.le hG]

end GlobalTheory.PoincareBounds
end
