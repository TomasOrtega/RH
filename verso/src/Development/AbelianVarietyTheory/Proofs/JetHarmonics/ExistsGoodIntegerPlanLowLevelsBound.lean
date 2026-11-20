import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OrbitSumFiftyOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.GoodPlan

/- English proof (translation)
Establish `hL` using `GlobalTheory.OrbitPlan.logTerm_nonneg hl hn`. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hl' : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hy0 : (0 : ℝ) ≤ y` using `Nat.cast_nonneg _`. Distinguish the cases in `hx : x = 0`.

Establish `: (y : ℝ) = 0` using `by nlinarith`. Establish `hy : y = 0` using `by exact_mod_cast this`. Simplify using `[blockBd, hy, hx]`. Rewrite using `[if_pos hx]`. Distinguish the cases in `hy : y = 0`.

Substitute `hy` using the available equality. Simplify using `only [blockBd, if_true, Nat.cast_zero, mul_zero, sub_zero] at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hiI : (i : ℝ) + 1 ≤ I` using `by exact_mod_cast hi hx`. Establish `hp : (1 : ℝ) ≤ (l : ℝ) ^ i` using `one_le_pow₀ (by linarith)`.

Establish `e : ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1) ≤ 2 * (I : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y)`. Rewrite using `[div_mul_eq_mul_div]`. Use `div_le_div_of_nonneg_right ?_ (by linarith)` and prove the remaining obligations. Establish `: ((i : ℝ) + 1) * ((l : ℝ) ^ i + 1) ≤ I * (2 * (l : ℝ) ^ i)` using `mul_le_mul hiI (by linarith) (by positivity) (by positivity)`. Establish `hmy : (0 : ℝ) ≤ m * y` using `by positivity`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right this hmy]`. Simplify using `only [blockBd, bdP, hy, if_false]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem blockBd_le {l n m i y I S : ℕ} {x : ℝ} (hl : 5 ≤ l) (hn : 1 ≤ n)
    (hi : x ≠ 0 → i < I) (h1 : (n : ℝ) * y ≤ x) (h2 : x - n * y ≤ n * S) :
    blockBd l n m i y ≤ n * gam l * ((l : ℝ) ^ i * y) + n * gam l * y - x +
      (if x ≠ 0 then (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) else 0) +
      2 * (I : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y) := by
  have hL := GlobalTheory.OrbitPlan.logTerm_nonneg hl hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  by_cases hx : x = 0
  · have : (y : ℝ) = 0 := by nlinarith
    have hy : y = 0 := by exact_mod_cast this
    simp [blockBd, hy, hx]
  rw [if_pos hx]
  by_cases hy : y = 0
  · subst hy
    simp only [blockBd, if_true, Nat.cast_zero, mul_zero, sub_zero] at h2 ⊢
    linarith
  have hiI : (i : ℝ) + 1 ≤ I := by exact_mod_cast hi hx
  have hp : (1 : ℝ) ≤ (l : ℝ) ^ i := one_le_pow₀ (by linarith)
  have e : ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1) ≤
      2 * (I : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y) := by
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (by linarith)
    have : ((i : ℝ) + 1) * ((l : ℝ) ^ i + 1) ≤ I * (2 * (l : ℝ) ^ i) :=
      mul_le_mul hiI (by linarith) (by positivity) (by positivity)
    have hmy : (0 : ℝ) ≤ m * y := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this hmy]
  simp only [blockBd, bdP, hy, if_false]
  linarith

/- English proof (translation)
Introduce `l d _ hl n m k S hn hk W Ws Good hW hG`. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hl' : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hW0 : (0 : ZMod d → ℝ) ≤ fun a => (n : ℝ) * Ws a` using `fun a => mul_nonneg hn0.le (hW a).1`.

Take `⟨ys, hflow, hsupp, hcard, hval⟩` from `GlobalTheory.BasicFlow.dropLevelsBasic l d (by omega) (fun a => (n : ℝ) * Ws a) hW0 (i0 k l)`. Take `⟨-, h3, -, hthl⟩` from `GlobalTheory.LevelsOrbits.thlEq k l hk (by omega)`. Establish `hex : ∀ a i, ∃ y : ℕ, (y ≠ 0 → y ∈ Good a i) ∧ (n : ℝ) * y ≤ ys a i ∧ ys a i - n * y ≤ n * (S : ℝ)`. Introduce `a i`. Distinguish the cases in `hc : i ∈ oddLevels d ∧ i < i0 k l`.

Take `⟨y, hy, h1, h2⟩` from `GlobalTheory.OrbitPlan.exists_good (hG a i hc.1 hc.2) (div_nonneg (hflow.1 a i) hn0.le)`. Rewrite `h1` using `[le_div_iff₀ hn0]`. Rewrite `h2` using `[sub_le_iff_le_add, div_le_iff₀ hn0]`. Conclude with `⟨y, fun _ => hy, by linarith, by linarith⟩`. Establish `: ys a i = 0` using `hsupp a i (by`.

Distinguish the cases in `h : i ∈ oddLevels d`. Use the proof step `left; by_contra h'; exact hc ⟨h, by omega⟩`. Use `right`. Conclude with `h)`. Use `⟨0, fun h => absurd rfl h, by simp [this], ?_⟩` and prove the remaining obligations.

Simplify using `only [this, Nat.cast_zero, mul_zero, sub_zero]`. Check the signs of the components of the expression. Use `choose y hyG hyle hyge using hex`. Establish `hy0 : ∀ a i, ys a i = 0 → y a i = 0`. Introduce `a i h`.

Establish `h1` using `hyle a i`. Rewrite `h1` using `[h]`. Establish `h2 : (0 : ℝ) ≤ y a i` using `Nat.cast_nonneg _`. Establish `: (y a i : ℝ) = 0` using `by nlinarith`. Conclude with `this` after adjusting the coercions.

Establish `hleR : ∀ a, (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) + (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ Ws a`. Introduce `a`. Use `le_of_mul_le_mul_left (le_trans ?_ (hflow.2 a)) hn0` and prove the remaining obligations. Rewrite using `[mul_add, Finset.mul_sum, Finset.mul_sum]`. Use `add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => hyle _ i)` and prove the remaining obligations.

Rewrite using `[mul_left_comm]`. Conclude with `mul_le_mul_of_nonneg_left (hyle a i) (by positivity)`. Establish `hle : ∀ a, (∑ i ∈ oddLevels d, l ^ i * y a i) + (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) ≤ W a`. Introduce `a`. Conclude with `(hleR a).trans (hW a).2` after adjusting the coercions.

Set `p : Plan l d W` to `{ y := y u := fun a => W a - ((∑ i ∈ oddLevels d, l ^ i * y a i) + (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i)) supp := fun a i hi => hy0 a i (hsupp a i (Or.inr hi)) bal := fun a => by have := hle a; omega }`. Use `⟨p, fun a i hi => hy0 a i (hsupp a i (Or.inl hi)), hyG, ?_⟩` and prove the remaining obligations. Establish `hbal : ∀ a, (W a : ℝ) = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) + (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + (p.u a : ℝ)`. Introduce `a`. Use `p.bal a` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Use `set L : ℝ := (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) with hL`. Establish `hL0 : 0 ≤ L`. Use `GlobalTheory.OrbitPlan.logTerm_nonneg hl hn` as an intermediate fact. Establish `: (0 : ℝ) ≤ n * S` using `by positivity`.

Rewrite using `[hL]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hshift : (∑ a, ∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) = ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)`. Rewrite using `[Finset.sum_comm, Finset.sum_comm (f := fun a i => (y a i : ℝ))]`. Conclude with `Finset.sum_congr rfl fun i _ => Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => (y a i : ℝ))`.

Use `set A : ℝ := ∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i with hA`. Use `set B : ℝ := ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ) with hB`. Use `set U : ℝ := ∑ a, (p.u a : ℝ) with hU`. Establish `hA0 : 0 ≤ A` using `by positivity`. Establish `hB0 : 0 ≤ B` using `by positivity`.

Establish `hsum : (∑ a, (W a : ℝ)) = A + B + U`. Rewrite using `[Finset.sum_congr rfl fun a _ => hbal a, Finset.sum_add_distrib, Finset.sum_add_distrib, hshift]`. Establish `hAB : A + B ≤ ∑ a, Ws a`. Use `Finset.sum_le_sum (s := Finset.univ) fun a _ => hleR a` as an intermediate fact. Rewrite `this` using `[Finset.sum_add_distrib, hshift]`. Then use the resulting hypothesis.

Establish `e1 : (∑ a, ∑ i ∈ oddLevels d, (if ys a i ≠ 0 then L else 0)) ≤ d * (i0 k l : ℝ) * L`. Rewrite using `[← Finset.sum_product' (f := fun a i => if ys a i ≠ 0 then L else 0), ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`. Use `mul_le_mul_of_nonneg_right ?_ hL0` and prove the remaining obligations. Conclude with `hcard.trans (Nat.le_mul_of_pos_right _ (by omega))` after adjusting the coercions. Use `set c : ℝ := 2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) with hc`.

Establish `hl1 : (0 : ℝ) < (l : ℝ) - 1` using `by linarith`. Establish `hc0 : 0 ≤ c` using `by positivity`. Establish `e2 : (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) ≤ n * gam l * A + n * gam l * B - flowVal d ys + (∑ a, ∑ i ∈ oddLevels d, (if ys a i ≠ 0 then L else 0)) + c * A`. Use `le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ => blockBd_le (I := i0 k l) (m := m) hl hn (fun h => by by_contra h'; exact h (hsupp a i (Or.inl (by omega)))) (hyle a i) (hyge a i)) (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, flowVal]`.

Both sides reduce to the same expression. Establish `e3 : (∑ a, chBd l n m (p.u a)) = n * gam l * U + m / ((l : ℝ) - 1) * U`. Simplify using `only [chBd, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : m / ((l : ℝ) - 1) * U ≤ m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1)`.

Rewrite using `[mul_div_right_comm]`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Establish `e5 : c * A ≤ 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1)`. Rewrite using `[mul_div_right_comm]`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) hc0`.

Rewrite `hval` using `[← Finset.mul_sum, ← inv_mul_eq_div, ← hthl]`. Unfold `Plan.bound Fnum`. Rewrite using `[e3, Finset.sum_sub_distrib, ← Finset.mul_sum]`. Express the relevant statement in the definitionally equal form `(∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) + _ ≤ _`. Rewrite `e4`, the goal using `[hsum]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_plan : ∀ (l d : ℕ) [NeZero d], 5 ≤ l → ∀ (n m k S : ℕ), 1 ≤ n → 1 ≤ k → ∀ (W : ZMod d → ℕ) (Ws : ZMod d → ℝ) (Good : ZMod d → ℕ → Set ℕ),
  (∀ a, 0 ≤ Ws a ∧ Ws a ≤ W a) → (∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows S (Good a i)) →
  ∃ p : Plan l d W, (∀ a i, i0 k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → p.y a i ∈ Good a i) ∧
    p.bound n m ≤ Fnum l d (fun a => (n : ℝ) * Ws a) + thl k l * n * (∑ a, Ws a) + n * gam l * (∑ a, ((W a : ℝ) - Ws a)) +
      m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) + 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) + d * (i0 k l : ℝ) * (n * ((S : ℝ) + Real.logb l n + 1)) := by
  intro l d _ hl n m k S hn hk W Ws Good hW hG
  classical
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hW0 : (0 : ZMod d → ℝ) ≤ fun a => (n : ℝ) * Ws a := fun a => mul_nonneg hn0.le (hW a).1
  obtain ⟨ys, hflow, hsupp, hcard, hval⟩ :=
    GlobalTheory.BasicFlow.dropLevelsBasic l d (by omega) (fun a => (n : ℝ) * Ws a) hW0 (i0 k l)
  obtain ⟨-, h3, -, hthl⟩ := GlobalTheory.LevelsOrbits.thlEq k l hk (by omega)
  have hex : ∀ a i, ∃ y : ℕ, (y ≠ 0 → y ∈ Good a i) ∧ (n : ℝ) * y ≤ ys a i ∧
      ys a i - n * y ≤ n * (S : ℝ) := by
    intro a i
    by_cases hc : i ∈ oddLevels d ∧ i < i0 k l
    · obtain ⟨y, hy, h1, h2⟩ := GlobalTheory.OrbitPlan.exists_good (hG a i hc.1 hc.2)
        (div_nonneg (hflow.1 a i) hn0.le)
      rw [le_div_iff₀ hn0] at h1
      rw [sub_le_iff_le_add, div_le_iff₀ hn0] at h2
      exact ⟨y, fun _ => hy, by linarith, by linarith⟩
    · have : ys a i = 0 := hsupp a i (by
        by_cases h : i ∈ oddLevels d
        · left; by_contra h'; exact hc ⟨h, by omega⟩
        · right; exact h)
      refine ⟨0, fun h => absurd rfl h, by simp [this], ?_⟩
      simp only [this, Nat.cast_zero, mul_zero, sub_zero]; positivity
  choose y hyG hyle hyge using hex
  have hy0 : ∀ a i, ys a i = 0 → y a i = 0 := by
    intro a i h
    have h1 := hyle a i
    rw [h] at h1
    have h2 : (0 : ℝ) ≤ y a i := Nat.cast_nonneg _
    have : (y a i : ℝ) = 0 := by nlinarith
    exact_mod_cast this
  have hleR : ∀ a, (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ Ws a := by
    intro a
    refine le_of_mul_le_mul_left (le_trans ?_ (hflow.2 a)) hn0
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => hyle _ i)
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hyle a i) (by positivity)
  have hle : ∀ a, (∑ i ∈ oddLevels d, l ^ i * y a i) +
      (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) ≤ W a := by
    intro a
    exact_mod_cast (hleR a).trans (hW a).2
  let p : Plan l d W :=
    { y := y
      u := fun a => W a - ((∑ i ∈ oddLevels d, l ^ i * y a i) +
        (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i))
      supp := fun a i hi => hy0 a i (hsupp a i (Or.inr hi))
      bal := fun a => by have := hle a; omega }
  refine ⟨p, fun a i hi => hy0 a i (hsupp a i (Or.inl hi)), hyG, ?_⟩
  have hbal : ∀ a, (W a : ℝ) = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + (p.u a : ℝ) := by
    intro a
    have := p.bal a
    exact_mod_cast this
  set L : ℝ := (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) with hL
  have hL0 : 0 ≤ L := by
    have := GlobalTheory.OrbitPlan.logTerm_nonneg hl hn
    have : (0 : ℝ) ≤ n * S := by positivity
    rw [hL]; linarith
  have hshift : (∑ a, ∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) =
      ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ) := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a i => (y a i : ℝ))]
    exact Finset.sum_congr rfl fun i _ =>
      Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => (y a i : ℝ))
  set A : ℝ := ∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i with hA
  set B : ℝ := ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ) with hB
  set U : ℝ := ∑ a, (p.u a : ℝ) with hU
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hsum : (∑ a, (W a : ℝ)) = A + B + U := by
    rw [Finset.sum_congr rfl fun a _ => hbal a, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hshift]
  have hAB : A + B ≤ ∑ a, Ws a := by
    have := Finset.sum_le_sum (s := Finset.univ) fun a _ => hleR a
    rwa [Finset.sum_add_distrib, hshift] at this
  have e1 : (∑ a, ∑ i ∈ oddLevels d, (if ys a i ≠ 0 then L else 0)) ≤ d * (i0 k l : ℝ) * L := by
    rw [← Finset.sum_product' (f := fun a i => if ys a i ≠ 0 then L else 0), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hL0
    exact_mod_cast hcard.trans (Nat.le_mul_of_pos_right _ (by omega))
  set c : ℝ := 2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) with hc
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hc0 : 0 ≤ c := by positivity
  have e2 : (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) ≤
      n * gam l * A + n * gam l * B - flowVal d ys +
        (∑ a, ∑ i ∈ oddLevels d, (if ys a i ≠ 0 then L else 0)) + c * A := by
    refine le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ =>
      blockBd_le (I := i0 k l) (m := m) hl hn
        (fun h => by by_contra h'; exact h (hsupp a i (Or.inl (by omega))))
        (hyle a i) (hyge a i)) (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, flowVal]
    rfl
  have e3 : (∑ a, chBd l n m (p.u a)) = n * gam l * U + m / ((l : ℝ) - 1) * U := by
    simp only [chBd, ← Finset.sum_mul]; ring
  have e4 : m / ((l : ℝ) - 1) * U ≤ m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e5 : c * A ≤ 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) hc0
  rw [← Finset.mul_sum, ← inv_mul_eq_div, ← hthl] at hval
  unfold Plan.bound Fnum
  rw [e3, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) + _ ≤ _
  rw [hsum] at e4 ⊢
  nlinarith

end GlobalTheory.GoodPlan
