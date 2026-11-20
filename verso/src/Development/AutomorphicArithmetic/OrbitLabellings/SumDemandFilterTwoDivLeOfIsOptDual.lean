import Mathlib
import Formalism.IncomingBounds.IncomingBound
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd
import Development.AutomorphicArithmetic.OrbitLabellings.ExistsMaxFlowAttainedAndIsOptDual

open scoped BigOperators
open Formalism.IncomingBounds

/- English proof (translation)
Introduce `l d _ hl D sig hD hopt`. Take `⟨⟨x, hx, hxv⟩, -⟩` from `UpperTheory.exists_maxFlow_attained_and_isOptDual l d hl D hD`. Establish `hl0 : (0 : ℝ) < l`. Establish `: (3 : ℝ) ≤ l` using `by exact_mod_cast hl`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hl1 : (1 : ℝ) ≤ l`. Establish `: (3 : ℝ) ≤ l` using `by exact_mod_cast hl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hin_nn : ∀ s : ZMod d, 0 ≤ ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i` using `fun s => Finset.sum_nonneg fun i _ => hx.1 _ _`. Establish `hF : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s ≤ flowVal d x`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Conclude with `(FlowDualityReindexing.fd_part1 hl D sig hopt s (Finset.mem_filter.mp hs).2 x hx hxv).2`. Use `_ ≤ ∑ s, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun s _ _ => hin_nn s`. Use `_ = flowVal d x := by`.

Unfold `flowVal`. Conclude with `FlowDualityReindexing.in_reindex x`. Establish `hout : ∀ s : ZMod d, (l : ℝ) * ∑ i ∈ oddLevels d, x s i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i`. Introduce `s`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Establish `hodd : Odd i` using `(Finset.mem_filter.mp hi).2`. Establish `hi1 : 1 ≤ i` using `hodd.pos`. Establish `hpow : (l : ℝ) ≤ (l : ℝ) ^ i`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `mul_le_mul_of_nonneg_right hpow (hx.1 s i)`. Establish `htot : (l : ℝ) * flowVal d x + flowVal d x ≤ ∑ s, D s`. Establish `h` using `Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => hx.2 s`. Rewrite `h` using `[Finset.sum_add_distrib, FlowDualityReindexing.in_reindex x]`. Establish `h2 : (l : ℝ) * flowVal d x ≤ ∑ s, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i`.

Unfold `flowVal`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_le_sum fun s _ => hout s`. Unfold `flowVal at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hFnn : 0 ≤ flowVal d x` using `Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => hx.1 _ _`. Rewrite using `[le_div_iff₀ hl0]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.sum_demand_filter_two_div_le_of_isOptDual :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → ∀ D sig : ZMod d → ℝ, 0 ≤ D → IsOptDual l d D sig →
    (∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s) ≤ (∑ s : ZMod d, D s) / l := by
  intro l d _ hl D sig hD hopt
  obtain ⟨⟨x, hx, hxv⟩, -⟩ := UpperTheory.exists_maxFlow_attained_and_isOptDual l d hl D hD
  have hl0 : (0 : ℝ) < l := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hl1 : (1 : ℝ) ≤ l := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hin_nn : ∀ s : ZMod d, 0 ≤ ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
    fun s => Finset.sum_nonneg fun i _ => hx.1 _ _
  have hF : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s ≤ flowVal d x := by
    calc ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s
        = ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s),
            ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := by
          refine Finset.sum_congr rfl fun s hs => ?_
          exact (FlowDualityReindexing.fd_part1 hl D sig hopt s (Finset.mem_filter.mp hs).2 x hx hxv).2
      _ ≤ ∑ s, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun s _ _ => hin_nn s
      _ = flowVal d x := by
          unfold flowVal
          exact FlowDualityReindexing.in_reindex x
  have hout : ∀ s : ZMod d, (l : ℝ) * ∑ i ∈ oddLevels d, x s i
      ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hodd : Odd i := (Finset.mem_filter.mp hi).2
    have hi1 : 1 ≤ i := hodd.pos
    have hpow : (l : ℝ) ≤ (l : ℝ) ^ i := by
      calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl1 hi1
    exact mul_le_mul_of_nonneg_right hpow (hx.1 s i)
  have htot : (l : ℝ) * flowVal d x + flowVal d x ≤ ∑ s, D s := by
    have h := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => hx.2 s
    rw [Finset.sum_add_distrib, FlowDualityReindexing.in_reindex x] at h
    have h2 : (l : ℝ) * flowVal d x ≤ ∑ s, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
      unfold flowVal
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ => hout s
    unfold flowVal at h2 ⊢
    linarith
  have hFnn : 0 ≤ flowVal d x :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => hx.1 _ _
  rw [le_div_iff₀ hl0]
  nlinarith
