import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulFlowValLe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ParametersSmallBoundStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSumsStatement

open scoped BigOperators
open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.OrbitPlan

/- English proof (translation)
Establish `h1` using `Nat.floor_le hr`. Establish `h2` using `Nat.lt_floor_add_one r`. Distinguish the cases in `hS : S ≤ ⌊r⌋₊ + 1`. Take `⟨y, hy, hy1, hy2⟩` from `h.2 (⌊r⌋₊ + 1 - S)`. Establish `a1 : y ≤ ⌊r⌋₊` using `by omega`.

Establish `a2 : ⌊r⌋₊ + 1 ≤ y + S` using `by omega`. Establish `b1 : (y : ℝ) ≤ ⌊r⌋₊` using `by exact_mod_cast a1`. Establish `b2 : (⌊r⌋₊ : ℝ) + 1 ≤ y + S` using `by exact_mod_cast a2`. Conclude with `⟨y, hy, by linarith, by linarith⟩`. Establish `a2 : ⌊r⌋₊ + 1 ≤ S` using `by omega`.

Establish `b2 : (⌊r⌋₊ : ℝ) + 1 ≤ S` using `by exact_mod_cast a2`. Conclude with `⟨0, h.1, by simpa using hr, by simp only [Nat.cast_zero]; linarith⟩`.
-/
theorem exists_good {S : ℕ} {G : Set ℕ} (h : Windows S G) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y ∈ G, (y : ℝ) ≤ r ∧ r - y ≤ S := by
  have h1 := Nat.floor_le hr
  have h2 := Nat.lt_floor_add_one r
  by_cases hS : S ≤ ⌊r⌋₊ + 1
  · obtain ⟨y, hy, hy1, hy2⟩ := h.2 (⌊r⌋₊ + 1 - S)
    have a1 : y ≤ ⌊r⌋₊ := by omega
    have a2 : ⌊r⌋₊ + 1 ≤ y + S := by omega
    have b1 : (y : ℝ) ≤ ⌊r⌋₊ := by exact_mod_cast a1
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ y + S := by exact_mod_cast a2
    exact ⟨y, hy, by linarith, by linarith⟩
  · have a2 : ⌊r⌋₊ + 1 ≤ S := by omega
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ S := by exact_mod_cast a2
    exact ⟨0, h.1, by simpa using hr, by simp only [Nat.cast_zero]; linarith⟩

/- English proof (translation)
Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast (by omega : 1 < l)`. Establish `h2 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Use `Real.logb_nonneg h1 h2` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem logTerm_nonneg {l n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) :
    0 ≤ (n : ℝ) * (Real.logb l n + 1) := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.logb_nonneg h1 h2
  positivity

/- English proof (translation)
Introduce `l d _ hp hl hd he n m k S hn hk hS W Good hG`. Establish `hW0 : (0 : ZMod d → ℝ) ≤ fun a => (W a : ℝ)` using `fun a => Nat.cast_nonneg _`. Take `⟨ys, hflow, hsupp, hcard, hval⟩` from `GlobalTheory.BasicFlow.main.1 l d (by omega) (fun a => (W a : ℝ)) hW0 (i0 k l)`. Take `⟨hodd, h3, -, hthl⟩` from `GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l hk (by omega)`. Establish `hex : ∀ a i, ∃ y : ℕ, (y ≠ 0 → y ∈ Good a i) ∧ (y : ℝ) ≤ ys a i ∧ ys a i - y ≤ (S : ℝ) + 1`.

Introduce `a i`. Distinguish the cases in `hc : i ∈ oddLevels d ∧ i < i0 k l`. Take `⟨y, hy, h1, h2⟩` from `exists_good (hG a i hc.1 hc.2) (hflow.1 a i)`. Conclude with `⟨y, fun _ => hy, h1, by linarith⟩`. Establish `: ys a i = 0` using `hsupp a i (by`.

Distinguish the cases in `h : i ∈ oddLevels d`. Use the proof step `left; by_contra h'; exact hc ⟨h, by omega⟩`. Use `right`. Conclude with `h)`. Use `⟨0, fun h => absurd rfl h, by simp [this], ?_⟩` and prove the remaining obligations.

Simplify using `only [this, Nat.cast_zero, sub_zero]`. Check the signs of the components of the expression. Use `choose y hyG hyle hyge using hex`. Establish `hy0 : ∀ a i, ys a i = 0 → y a i = 0`. Introduce `a i h`.

Use `hyle a i` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `le_antisymm this (Nat.cast_nonneg _)` after adjusting the coercions. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (by omega : 0 < l)`. Establish `hl1 : (0 : ℝ) < (l : ℝ) - 1`.

Establish `: (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : ∀ a, (∑ i ∈ oddLevels d, l ^ i * y a i) + (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) ≤ W a`. Introduce `a`. Establish `h1 : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * ys a i` using `Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyle a i) (by positivity)`.

Establish `h2 : (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ ∑ i ∈ oddLevels d, ys (a - (i : ZMod d)) i` using `Finset.sum_le_sum fun i _ => hyle _ i`. Establish `h3` using `hflow.2 a`. Establish `: (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) + (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ (W a : ℝ)`. Simplify using `only at h3`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `this` after adjusting the coercions. Set `p : Plan l d W` to `{ y := y u := fun a => W a - ((∑ i ∈ oddLevels d, l ^ i * y a i) + (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i)) supp := fun a i hi => hy0 a i (hsupp a i (Or.inr hi)) bal := fun a => by have := hle a; omega }`. Establish `hcard' : (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter fun x => y x.1 x.2 ≠ 0).card ≤ d`. Use `le_trans (Finset.card_le_card ?_) hcard` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx`, the goal using `[Finset.mem_filter]`. Conclude with `⟨hx.1, fun h => hx.2 (hy0 _ _ h)⟩`. Use `⟨p, ⟨fun a i hi => hy0 a i (hsupp a i (Or.inl hi)), hyG, hcard'⟩, ?_⟩` and prove the remaining obligations. Establish `hbal : ∀ a, (W a : ℝ) = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) + (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + (p.u a : ℝ)`. Introduce `a`.

Use `p.bal a` as an intermediate fact. Conclude with `this` after adjusting the coercions. Use `set L : ℝ := (n : ℝ) * (Real.logb l n + 1) with hL`. Establish `hL0 : 0 ≤ L` using `logTerm_nonneg hl hn`. Establish `key` using `GlobalTheory.T.sizeData_small_bound l d (by omega) hd n m (thl k l) ((S : ℝ) + 1) (fun a => (W a : ℝ)) ys y (fun a => (p.u a : ℝ)) (fun _ => 0) (fun a => chBd l n m (p.u a)) (fun _ => 0) (fun a i => blockBd l n m i (y a i)) (fun a i => (if y a i ≠ 0 then L else 0) + ((i : ℝ) + 1) …`.

Distinguish the cases in `h : y a i = 0`. Simplify using `[blockBd, h]`. Simplify using `only [blockBd, bdP, h, if_false, ne_eq, not_false_eq_true, if_true, hL] linarith)`. Use the proof step `(fun a => le_rfl) (fun _ => by simp)`. Simplify using `only [Finset.sum_const_zero, add_zero, zero_div, Finset.sum_add_distrib] at key`.

Establish `e1 : (∑ a, ∑ i ∈ oddLevels d, (if y a i ≠ 0 then L else 0)) ≤ d * L`. Rewrite using `[← Finset.sum_product' (f := fun a i => if y a i ≠ 0 then L else 0), ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`. Conclude with `mul_le_mul_of_nonneg_right (by exact_mod_cast hcard') hL0`. Establish `e2 : (n : ℝ) * ((S : ℝ) + 1) * (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter (fun p => ys p.1 p.2 ≠ 0)).card ≤ n * ((S : ℝ) + 1) * d` using `mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)`. Establish `hi3 : (3 : ℝ) ≤ i0 k l` using `by exact_mod_cast h3`.

Establish `hrow : ∀ a, (∑ i ∈ oddLevels d, ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y a i / ((l : ℝ) - 1)) ≤ (2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)) * W a`. Introduce `a`. Establish `c0 : 0 ≤ 2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)` using `div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hl1.le`. Establish `h1 : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤ W a`. Establish `: (∑ i ∈ oddLevels d, l ^ i * y a i) ≤ W a` using `le_trans (Nat.le_add_right _ _) (hle a)`.

Conclude with `this` after adjusting the coercions. Use `le_trans ?_ (mul_le_mul_of_nonneg_left h1 c0)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `h : y a i = 0`.

Simplify using `[h]`. Establish `hi1 : i < i0 k l`. Assume the negation of the conclusion as `h'`. Conclude with `h (hy0 a i (hsupp a i (Or.inl (by omega))))`. Establish `hio : Odd i` using `(Finset.mem_filter.1 hi).2`.

Establish `hi2 : i + 2 ≤ i0 k l`. Take `⟨s, hs⟩` from `hio`. Take `⟨t, ht⟩` from `hodd`. Use linear arithmetic over natural numbers and integers. Establish `hi2' : (i : ℝ) + 1 ≤ (i0 k l : ℝ) - 1`.

Establish `: (i : ℝ) + 2 ≤ i0 k l` using `by exact_mod_cast hi2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpow : (1 : ℝ) ≤ (l : ℝ) ^ i` using `one_le_pow₀ (by linarith)`. Rewrite using `[div_mul_eq_mul_div]`. Use `div_le_div_of_nonneg_right ?_ hl1.le` and prove the remaining obligations.

Establish `q : ((i : ℝ) + 1) * ((l : ℝ) ^ i + 1) ≤ ((i0 k l : ℝ) - 1) * (2 * (l : ℝ) ^ i)` using `mul_le_mul hi2' (by linarith) (by positivity) (by linarith)`. Use `mul_le_mul_of_nonneg_right q (show (0 : ℝ) ≤ (m : ℝ) * y a i by positivity)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3` using `Finset.sum_le_sum fun a (_ : a ∈ (Finset.univ : Finset (ZMod d))) => hrow a`. Rewrite `e3` using `[← Finset.mul_sum]`.

Establish `e4 : (m : ℝ) * (∑ a, (p.u a : ℝ)) / ((l : ℝ) - 1) ≤ m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1)`. Use `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)) hl1.le` and prove the remaining obligations. Conclude with `Nat.sub_le _ _` after adjusting the coercions. Establish `e5 : (2 * (i0 k l : ℝ) - 1) * m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) = (2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)) * (∑ a, (W a : ℝ)) + m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1)` using `by ring`. Rewrite using `[e5]`.

Express the relevant statement in the definitionally equal form `(∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) + ∑ a, chBd l n m (p.u a) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem orbit_sum_fifty_one : WindowedChoiceExistsWithBound := by
  intro l d _ hp hl hd he n m k S hn hk hS W Good hG
  classical
  have hW0 : (0 : ZMod d → ℝ) ≤ fun a => (W a : ℝ) := fun a => Nat.cast_nonneg _
  obtain ⟨ys, hflow, hsupp, hcard, hval⟩ :=
    GlobalTheory.BasicFlow.main.1 l d (by omega) (fun a => (W a : ℝ)) hW0 (i0 k l)
  obtain ⟨hodd, h3, -, hthl⟩ := GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l hk (by omega)
  have hex : ∀ a i, ∃ y : ℕ, (y ≠ 0 → y ∈ Good a i) ∧ (y : ℝ) ≤ ys a i ∧
      ys a i - y ≤ (S : ℝ) + 1 := by
    intro a i
    by_cases hc : i ∈ oddLevels d ∧ i < i0 k l
    · obtain ⟨y, hy, h1, h2⟩ := exists_good (hG a i hc.1 hc.2) (hflow.1 a i)
      exact ⟨y, fun _ => hy, h1, by linarith⟩
    · have : ys a i = 0 := hsupp a i (by
        by_cases h : i ∈ oddLevels d
        · left; by_contra h'; exact hc ⟨h, by omega⟩
        · right; exact h)
      refine ⟨0, fun h => absurd rfl h, by simp [this], ?_⟩
      simp only [this, Nat.cast_zero, sub_zero]; positivity
  choose y hyG hyle hyge using hex
  have hy0 : ∀ a i, ys a i = 0 → y a i = 0 := by
    intro a i h
    have := hyle a i
    rw [h] at this
    exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hle : ∀ a, (∑ i ∈ oddLevels d, l ^ i * y a i) +
      (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) ≤ W a := by
    intro a
    have h1 : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * ys a i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyle a i) (by positivity)
    have h2 : (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤
        ∑ i ∈ oddLevels d, ys (a - (i : ZMod d)) i :=
      Finset.sum_le_sum fun i _ => hyle _ i
    have h3 := hflow.2 a
    have : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ (W a : ℝ) := by
      simp only at h3
      linarith
    exact_mod_cast this
  let p : Plan l d W :=
    { y := y
      u := fun a => W a - ((∑ i ∈ oddLevels d, l ^ i * y a i) +
        (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i))
      supp := fun a i hi => hy0 a i (hsupp a i (Or.inr hi))
      bal := fun a => by have := hle a; omega }
  have hcard' : (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
      fun x => y x.1 x.2 ≠ 0).card ≤ d := by
    refine le_trans (Finset.card_le_card ?_) hcard
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, fun h => hx.2 (hy0 _ _ h)⟩
  refine ⟨p, ⟨fun a i hi => hy0 a i (hsupp a i (Or.inl hi)), hyG, hcard'⟩, ?_⟩
  have hbal : ∀ a, (W a : ℝ) = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + (p.u a : ℝ) := by
    intro a
    have := p.bal a
    exact_mod_cast this
  set L : ℝ := (n : ℝ) * (Real.logb l n + 1) with hL
  have hL0 : 0 ≤ L := logTerm_nonneg hl hn
  have key := GlobalTheory.T.sizeData_small_bound l d (by omega) hd n m (thl k l) ((S : ℝ) + 1) (fun a => (W a : ℝ)) ys y
    (fun a => (p.u a : ℝ)) (fun _ => 0) (fun a => chBd l n m (p.u a)) (fun _ => 0)
    (fun a i => blockBd l n m i (y a i))
    (fun a i => (if y a i ≠ 0 then L else 0) +
      ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y a i / ((l : ℝ) - 1))
    hW0 hflow (by rw [hthl, inv_mul_eq_div]; exact hval) hyle hyge hy0
    (fun a => Nat.cast_nonneg _) (fun _ => le_rfl) (fun a => by rw [add_zero]; exact hbal a)
    (fun a i _ => by
      by_cases h : y a i = 0
      · simp [blockBd, h]
      · simp only [blockBd, bdP, h, if_false, ne_eq, not_false_eq_true, if_true, hL]
        linarith)
    (fun a => le_rfl) (fun _ => by simp)
  simp only [Finset.sum_const_zero, add_zero, zero_div, Finset.sum_add_distrib] at key

  have e1 : (∑ a, ∑ i ∈ oddLevels d, (if y a i ≠ 0 then L else 0)) ≤ d * L := by
    rw [← Finset.sum_product' (f := fun a i => if y a i ≠ 0 then L else 0), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard') hL0
  have e2 : (n : ℝ) * ((S : ℝ) + 1) * (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
      (fun p => ys p.1 p.2 ≠ 0)).card ≤ n * ((S : ℝ) + 1) * d :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)
  have hi3 : (3 : ℝ) ≤ i0 k l := by exact_mod_cast h3
  have hrow : ∀ a, (∑ i ∈ oddLevels d,
      ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y a i / ((l : ℝ) - 1)) ≤
      (2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)) * W a := by
    intro a
    have c0 : 0 ≤ 2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) :=
      div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hl1.le
    have h1 : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤ W a := by
      have : (∑ i ∈ oddLevels d, l ^ i * y a i) ≤ W a := le_trans (Nat.le_add_right _ _) (hle a)
      exact_mod_cast this
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 c0)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases h : y a i = 0
    · simp [h]
    have hi1 : i < i0 k l := by
      by_contra h'
      exact h (hy0 a i (hsupp a i (Or.inl (by omega))))
    have hio : Odd i := (Finset.mem_filter.1 hi).2
    have hi2 : i + 2 ≤ i0 k l := by
      obtain ⟨s, hs⟩ := hio
      obtain ⟨t, ht⟩ := hodd
      omega
    have hi2' : (i : ℝ) + 1 ≤ (i0 k l : ℝ) - 1 := by
      have : (i : ℝ) + 2 ≤ i0 k l := by exact_mod_cast hi2
      linarith
    have hpow : (1 : ℝ) ≤ (l : ℝ) ^ i := one_le_pow₀ (by linarith)
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hl1.le
    have q : ((i : ℝ) + 1) * ((l : ℝ) ^ i + 1) ≤ ((i0 k l : ℝ) - 1) * (2 * (l : ℝ) ^ i) :=
      mul_le_mul hi2' (by linarith) (by positivity) (by linarith)
    have := mul_le_mul_of_nonneg_right q (show (0 : ℝ) ≤ (m : ℝ) * y a i by positivity)
    linarith
  have e3 := Finset.sum_le_sum fun a (_ : a ∈ (Finset.univ : Finset (ZMod d))) => hrow a
  rw [← Finset.mul_sum] at e3
  have e4 : (m : ℝ) * (∑ a, (p.u a : ℝ)) / ((l : ℝ) - 1) ≤ m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) := by
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)) hl1.le
    exact_mod_cast Nat.sub_le _ _
  have e5 : (2 * (i0 k l : ℝ) - 1) * m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) =
      (2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)) * (∑ a, (W a : ℝ)) +
        m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) := by ring
  rw [e5]
  change (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) + ∑ a, chBd l n m (p.u a) ≤ _
  linarith

/- English proof (translation)
Introduce `l d _ hp hl hd he n m k S hn hk hS W Good T θ w th hG hT hw hTW hth hθ`. Take `⟨p, hok, hb⟩` from `orbit_sum_fifty_one l d hp hl hd he n m k S hn hk hS W Good hG`. Use `⟨p, hok, ?_⟩` and prove the remaining obligations. Establish `hs` using `GlobalTheory.FlowScaling.main.2.1 l d (by omega) hd he n T θ w (fun a => (W a : ℝ)) th hT hw hTW hth hθ`. Take `⟨-, h3, -, hthl⟩` from `GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l hk (by omega)`.

Establish `hi3 : (3 : ℝ) ≤ i0 k l` using `by exact_mod_cast h3`. Establish `hl1 : (0 : ℝ) < (l : ℝ) - 1`. Establish `: (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht0 : 0 ≤ thl k l` using `by rw [hthl]; positivity`.

Establish `hsum : T * (∑ a, (W a : ℝ)) ≤ ∑ a, w a`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hTW a]`. Use `mul_nonneg (hw a).le (hth a).1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `c0 : 0 ≤ (2 * (i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)` using `div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hl1.le`. Establish `e1` using `mul_le_mul_of_nonneg_left hsum c0`. Establish `e2` using `mul_le_mul_of_nonneg_left hsum (mul_nonneg ht0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))`. Establish `e3` using `mul_le_mul_of_nonneg_left hb hT.le`.

Establish `e4 : ∀ x : ℝ, (2 * (i0 k l : ℝ) - 1) * m * x / ((l : ℝ) - 1) = (2 * (i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) * x` using `fun x => by ring`. Rewrite `e3`, the goal using `[e4]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem contentOrbit : ContentOrbit := by
  intro l d _ hp hl hd he n m k S hn hk hS W Good T θ w th hG hT hw hTW hth hθ
  obtain ⟨p, hok, hb⟩ := orbit_sum_fifty_one l d hp hl hd he n m k S hn hk hS W Good hG
  refine ⟨p, hok, ?_⟩
  have hs := GlobalTheory.FlowScaling.main.2.1 l d (by omega) hd he n T θ w (fun a => (W a : ℝ)) th hT hw hTW
    hth hθ
  obtain ⟨-, h3, -, hthl⟩ := GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l hk (by omega)
  have hi3 : (3 : ℝ) ≤ i0 k l := by exact_mod_cast h3
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have ht0 : 0 ≤ thl k l := by rw [hthl]; positivity
  have hsum : T * (∑ a, (W a : ℝ)) ≤ ∑ a, w a := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [hTW a]
    have := mul_nonneg (hw a).le (hth a).1
    linarith
  have c0 : 0 ≤ (2 * (i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hl1.le
  have e1 := mul_le_mul_of_nonneg_left hsum c0
  have e2 := mul_le_mul_of_nonneg_left hsum (mul_nonneg ht0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  have e3 := mul_le_mul_of_nonneg_left hb hT.le
  have e4 : ∀ x : ℝ, (2 * (i0 k l : ℝ) - 1) * m * x / ((l : ℝ) - 1) =
      (2 * (i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) * x := fun x => by ring
  rw [e4] at e3 ⊢
  nlinarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨orbit_sum_fifty_one, contentOrbit⟩`.
-/
theorem main : WindowedChoiceExistsWithBound ∧ ContentOrbit := ⟨orbit_sum_fifty_one, contentOrbit⟩

end GlobalTheory.OrbitPlan
