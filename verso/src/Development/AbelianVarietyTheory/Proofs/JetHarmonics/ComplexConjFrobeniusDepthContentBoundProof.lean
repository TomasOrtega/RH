import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttainedStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypingsStatement

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators

namespace GlobalTheory.GoodDepth.ConjPkg

/- English proof (translation)
Establish `hd` using `Nat.div_add_mod W (l + 1)`. Establish `hm` using `Nat.mod_lt W (Nat.succ_pos l)`. Use `set q := W / (l + 1)`. Use `set r := W % (l + 1)`. Distinguish the cases in `hq : q + 1 ≤ S`.

Use `⟨0, W, by simp, h.1, ?_⟩` and prove the remaining obligations. Establish `: (l + 1) * (q + 1) ≤ (l + 1) * S` using `Nat.mul_le_mul_left _ hq`. Rewrite `this` using `[Nat.mul_add]`. Use linear arithmetic over natural numbers and integers. Take `⟨y, hy, h1, h2⟩` from `h.2 (q + 1 - S)`.

Take `⟨c, hc⟩ : ∃ c, q = y + c` from `⟨q - y, by omega⟩`. Use `⟨y, (l + 1) * c + r, ?_, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← hd, hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `: (l + 1) * (c + 1) ≤ (l + 1) * S` using `Nat.mul_le_mul_left _ (by omega)`.

Rewrite `this` using `[Nat.mul_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_good (l S W : ℕ) (G : Set ℕ) (h : RF.Windows S G) :
    ∃ y u : ℕ, W = (l + 1) * y + u ∧ y ∈ G ∧ u ≤ (l + 1) * S := by
  have hd := Nat.div_add_mod W (l + 1)
  have hm := Nat.mod_lt W (Nat.succ_pos l)
  set q := W / (l + 1)
  set r := W % (l + 1)
  by_cases hq : q + 1 ≤ S
  · refine ⟨0, W, by simp, h.1, ?_⟩
    have : (l + 1) * (q + 1) ≤ (l + 1) * S := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_add] at this
    omega
  · obtain ⟨y, hy, h1, h2⟩ := h.2 (q + 1 - S)
    obtain ⟨c, hc⟩ : ∃ c, q = y + c := ⟨q - y, by omega⟩
    refine ⟨y, (l + 1) * c + r, ?_, hy, ?_⟩
    · rw [← hd, hc]; ring
    · have : (l + 1) * (c + 1) ≤ (l + 1) * S := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add] at this
      omega

/- English proof (translation)
Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_log (x : ℝ) (hx : 4 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/- English proof (translation)
Establish `h1 : 1 ≤ Real.log l` using `one_le_log _ (by exact_mod_cast (by omega : 4 ≤ l))`. Establish `h2 : 0 ≤ Real.log x` using `Real.log_nonneg hx`. Unfold `Real.logb`. Conclude with `div_le_self h2 h1`.
-/
theorem logb_le_log (l : ℕ) (hl : 5 ≤ l) (x : ℝ) (hx : 1 ≤ x) : Real.logb l x ≤ Real.log x := by
  have h1 : 1 ≤ Real.log l := one_le_log _ (by exact_mod_cast (by omega : 4 ≤ l))
  have h2 : 0 ≤ Real.log x := Real.log_nonneg hx
  unfold Real.logb
  exact div_le_self h2 h1

/- English proof (translation)
Establish `hl' : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hu' : (u : ℝ) ≤ (l + 1) * S` using `by exact_mod_cast hu`. Establish `hlog : 0 ≤ Real.logb l n` using `Real.logb_nonneg (by linarith) hn'`. Establish `h1 : (0 : ℝ) < (l : ℝ) - 1` using `by linarith`.

Establish `h2 : (0 : ℝ) < (l : ℝ) + 1` using `by linarith`. Establish `h3 : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * (l + 1)` using `by ring`. Establish `hy0 : (0 : ℝ) ≤ y` using `Nat.cast_nonneg _`. Establish `hu0 : (0 : ℝ) ≤ u` using `Nat.cast_nonneg _`. Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg _`.

Establish `hS0 : (0 : ℝ) ≤ S` using `Nat.cast_nonneg _`. Establish `hrho : 0 ≤ Formalism.IncomingBounds.rho l` using `by unfold Formalism.IncomingBounds.rho; rw [h3]; positivity`. Establish `hb : RF.blockBd l n m 1 y ≤ Formalism.IncomingBounds.rho l * n * ((l + 1) * y) + n * (Real.logb l n + 1) + 2 * m * ((l + 1) * y) / ((l : ℝ) - 1)`. Unfold `RF.blockBd`. Use `split_ifs with h`.

Check the signs of the components of the expression. Apply `le_of_eq` to reduce the goal to its premises. Unfold `bdP Formalism.IncomingBounds.gam Formalism.IncomingBounds.rho`. Rewrite using `[h3]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hc : RF.chBd l n m u ≤ 2 * n * S + m * u / ((l : ℝ) - 1)`. Unfold `RF.chBd Formalism.IncomingBounds.gam`. Establish `: (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1))) ≤ 2 * n * S`. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul_of_nonneg_right hu'` to reduce the goal to its premises. Rewrite using `[h3]`. Check the signs of the components of the expression. Use `_ = n * S * ((l : ℝ) / ((l : ℝ) - 1)) := by rw [h3]; field_simp`. Use `_ ≤ n * S * 2 := by`.

Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Rewrite using `[div_le_iff₀ h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = _ := by ring`. Establish `e : (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1)) + m / ((l : ℝ) - 1)) = (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1))) + m * u / ((l : ℝ) - 1)` using `by ring`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : 2 * m * ((l + 1) * y) / ((l : ℝ) - 1) + m * u / ((l : ℝ) - 1) ≤ 4 * m * ((l + 1) * y + u) / l`. Establish `hi : 1 / ((l : ℝ) - 1) ≤ 2 / l`. Rewrite using `[div_le_div_iff₀ h1 (by linarith)]; linarith`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul _ hi (by positivity) (by positivity)` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_nonneg hm0 hu0]`. Use `_ = _ := by ring`. Establish `he : 0 ≤ Formalism.IncomingBounds.rho l * n * u` using `by positivity`.

Use `push_cast`. Establish `e2 : Formalism.IncomingBounds.rho l * n * (((l : ℝ) + 1) * y + u) = Formalism.IncomingBounds.rho l * n * ((l + 1) * y) + Formalism.IncomingBounds.rho l * n * u` using `by ring`. Rewrite using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem place_bound (l n m S y u : ℕ) (hl : 5 ≤ l) (hn : 1 ≤ n) (hu : u ≤ (l + 1) * S) :
    RF.blockBd l n m 1 y + RF.chBd l n m u ≤
      Formalism.IncomingBounds.rho l * n * (((l + 1) * y + u : ℕ) : ℝ) + 4 * m * (((l + 1) * y + u : ℕ) : ℝ) / l +
        (n * (Real.logb l n + 1) + 2 * n * S) := by
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hu' : (u : ℝ) ≤ (l + 1) * S := by exact_mod_cast hu
  have hlog : 0 ≤ Real.logb l n := Real.logb_nonneg (by linarith) hn'
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have h3 : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * (l + 1) := by ring
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hrho : 0 ≤ Formalism.IncomingBounds.rho l := by unfold Formalism.IncomingBounds.rho; rw [h3]; positivity
  have hb : RF.blockBd l n m 1 y ≤ Formalism.IncomingBounds.rho l * n * ((l + 1) * y) + n * (Real.logb l n + 1) +
      2 * m * ((l + 1) * y) / ((l : ℝ) - 1) := by
    unfold RF.blockBd
    split_ifs with h
    · positivity
    · apply le_of_eq
      unfold bdP Formalism.IncomingBounds.gam Formalism.IncomingBounds.rho
      rw [h3]
      field_simp
      ring
  have hc : RF.chBd l n m u ≤ 2 * n * S + m * u / ((l : ℝ) - 1) := by
    unfold RF.chBd Formalism.IncomingBounds.gam
    have : (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1))) ≤ 2 * n * S := by
      calc (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1)))
          ≤ ((l + 1) * S) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1))) := by
            apply mul_le_mul_of_nonneg_right hu'; rw [h3]; positivity
        _ = n * S * ((l : ℝ) / ((l : ℝ) - 1)) := by rw [h3]; field_simp
        _ ≤ n * S * 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_iff₀ h1]; linarith
        _ = _ := by ring
    have e : (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1)) + m / ((l : ℝ) - 1)) =
        (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1))) + m * u / ((l : ℝ) - 1) := by ring
    rw [e]; linarith
  have hd : 2 * m * ((l + 1) * y) / ((l : ℝ) - 1) + m * u / ((l : ℝ) - 1) ≤
      4 * m * ((l + 1) * y + u) / l := by
    have hi : 1 / ((l : ℝ) - 1) ≤ 2 / l := by
      rw [div_le_div_iff₀ h1 (by linarith)]; linarith
    calc 2 * m * ((l + 1) * y) / ((l : ℝ) - 1) + m * u / ((l : ℝ) - 1)
        = (2 * m * ((l + 1) * y) + m * u) * (1 / ((l : ℝ) - 1)) := by ring
      _ ≤ (2 * m * ((l + 1) * y) + 2 * m * u) * (2 / l) := by
          apply mul_le_mul _ hi (by positivity) (by positivity)
          nlinarith [mul_nonneg hm0 hu0]
      _ = _ := by ring
  have he : 0 ≤ Formalism.IncomingBounds.rho l * n * u := by positivity
  push_cast
  have e2 : Formalism.IncomingBounds.rho l * n * (((l : ℝ) + 1) * y + u) =
      Formalism.IncomingBounds.rho l * n * ((l + 1) * y) + Formalism.IncomingBounds.rho l * n * u := by ring
  rw [e2]
  linarith

/- English proof (translation)
Establish `hl' : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hn' : (3 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hL : 1 ≤ Real.log ((n : ℝ) + 1)` using `one_le_log _ (by linarith)`. Establish `h1 : Real.logb l n ≤ Real.log ((n : ℝ) + 1)` using `(logb_le_log l hl _ (by linarith)).trans (Real.log_le_log (by linarith) (by linarith))`. Establish `h2 : Real.logb l ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1)` using `logb_le_log l hl _ (by linarith)`.

Establish `h2' : 0 ≤ Real.logb l ((n : ℝ) + 1)` using `Real.logb_nonneg (by linarith) (by linarith)`. Use `set L := Real.log ((n : ℝ) + 1)`. Establish `hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2` using `by nlinarith`. Establish `hnL : 1 ≤ (n : ℝ) ^ 2 * L` using `by nlinarith`. Establish `hnL' : L ≤ (n : ℝ) ^ 2 * L` using `by nlinarith`.

Establish `hS : (S0 l 1 n : ℝ) ≤ 449 * ((n : ℝ) ^ 2 * L)`. Unfold `S0`. Use `Nat.ceil_lt_add_one (a := 64 * (n : ℝ) ^ 2 * (((1 : ℕ) : ℝ) + 3 + 3 * Real.logb l ((n : ℝ) + 1))) (by positivity)` as an intermediate fact. Establish `h4 : 64 * (n : ℝ) ^ 2 * (((1 : ℕ) : ℝ) + 3 + 3 * Real.logb l ((n : ℝ) + 1)) ≤ 64 * (n : ℝ) ^ 2 * (7 * L)`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Establish `: Real.logb l n + 1 + 2 * (S0 l 1 n : ℝ) ≤ 900 * ((n : ℝ) ^ 2 * L)` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem additive_bound (l n : ℕ) (hl : 5 ≤ l) (hn : 3 ≤ n) :
    (n : ℝ) * (Real.logb l n + 1) + 2 * n * (S0 l 1 n : ℝ) ≤ 900 * ((n : ℝ) ^ 3 * Real.log ((n : ℝ) + 1)) := by
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 1 ≤ Real.log ((n : ℝ) + 1) := one_le_log _ (by linarith)
  have h1 : Real.logb l n ≤ Real.log ((n : ℝ) + 1) :=
    (logb_le_log l hl _ (by linarith)).trans (Real.log_le_log (by linarith) (by linarith))
  have h2 : Real.logb l ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) := logb_le_log l hl _ (by linarith)
  have h2' : 0 ≤ Real.logb l ((n : ℝ) + 1) := Real.logb_nonneg (by linarith) (by linarith)
  set L := Real.log ((n : ℝ) + 1)
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnL : 1 ≤ (n : ℝ) ^ 2 * L := by nlinarith
  have hnL' : L ≤ (n : ℝ) ^ 2 * L := by nlinarith
  have hS : (S0 l 1 n : ℝ) ≤ 449 * ((n : ℝ) ^ 2 * L) := by
    unfold S0
    have := Nat.ceil_lt_add_one (a := 64 * (n : ℝ) ^ 2 * (((1 : ℕ) : ℝ) + 3 + 3 * Real.logb l ((n : ℝ) + 1)))
      (by positivity)
    have h4 : 64 * (n : ℝ) ^ 2 * (((1 : ℕ) : ℝ) + 3 + 3 * Real.logb l ((n : ℝ) + 1)) ≤ 64 * (n : ℝ) ^ 2 * (7 * L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      push_cast; linarith
    nlinarith
  have : Real.logb l n + 1 + 2 * (S0 l 1 n : ℝ) ≤ 900 * ((n : ℝ) ^ 2 * L) := by linarith
  calc _ = (n : ℝ) * (Real.logb l n + 1 + 2 * (S0 l 1 n : ℝ)) := by ring
    _ ≤ n * (900 * ((n : ℝ) ^ 2 * L)) := mul_le_mul_of_nonneg_left this (by linarith)
    _ = _ := by ring

/- English proof (translation)
Unfold `thl`. Apply `Real.sSup_nonneg` to reduce the goal to its premises. Introduce and unpack `t ⟨i, -, -, -, rfl⟩`. Check the signs of the components of the expression.
-/
theorem thl_nonneg (k l : ℕ) : 0 ≤ thl k l := by
  unfold thl
  apply Real.sSup_nonneg
  rintro t ⟨i, -, -, -, rfl⟩
  positivity

/- English proof (translation)
Establish `h0 : X.big 0 0` using `(h.2 0).2 (by decide)`. Establish `h1 : ¬ X.big 0 1` using `fun hb => absurd ((h.2 1).1 hb) (by decide)`. Conclude with `⟨h0, X.rk_big 0 0 h0, X.rk_small 0 1 h1⟩`.
-/
theorem rk_alt {C : Type} [Field C] {V : VF C} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V 2 I J) (h : X.Alt) : X.big 0 0 ∧ X.rkF 0 0 = X.n + X.j ∧ X.rkF 0 1 = X.j' := by
  have h0 : X.big 0 0 := (h.2 0).2 (by decide)
  have h1 : ¬ X.big 0 1 := fun hb => absurd ((h.2 1).1 hb) (by decide)
  exact ⟨h0, X.rk_big 0 0 h0, X.rk_small 0 1 h1⟩

def expEven (n x : ℕ) (ga : ZMod 2 → ℕ → ℕ) : ZMod 2 → ℕ → ℕ :=
  fun a k => if a = 0 then (if k = n then x else ga 0 k) else 0

def expOdd (ga : ZMod 2 → ℕ → ℕ) : ZMod 2 → ℕ → ℕ := fun a k => if a = 1 then ga 1 k else 0

/- English proof (translation)
The claim follows from `Fin.sum_univ_two f`.
-/
theorem sum_two (f : ZMod 2 → ℝ) : ∑ a, f a = f 0 + f 1 := Fin.sum_univ_two f
/- English proof (translation)
The claim follows from `Fin.sum_univ_two f`.
-/
theorem sum_two' (f : ZMod 2 → ℕ) : ∑ a, f a = f 0 + f 1 := Fin.sum_univ_two f

/- English proof (translation)
Unfold `monDeg`. Use `push_cast`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (min_le_left _ _)) (fun _ _ _ => by positivity)`.
-/
theorem monDeg_le (N N' : ℕ) (e : ℕ → ℕ) : (monDeg N N' e : ℝ) ≤ ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * e k := by
  unfold monDeg
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (min_le_left _ _))
    (fun _ _ _ => by positivity)

/- English proof (translation)
Establish `h10 : (1 : ZMod 2) ≠ 0` using `by decide`. Unfold `RF.monDegAll`. Rewrite using `[sum_two', sum_two', sum_two]`. Use `push_cast`. Establish `a1` using `monDeg_le r (X.rkF 0 0) (expEven n x ga 0)`.

Establish `a2` using `monDeg_le r (X.rkF 0 1) (expEven n x ga 1)`. Establish `a3` using `monDeg_le r (X.rkF 0 0) (expOdd ga 0)`. Establish `a4` using `monDeg_le r (X.rkF 0 1) (expOdd ga 1)`. Establish `b2 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expEven n x ga 1 k) = 0` using `by simp [expEven, h10]`. Establish `b3 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expOdd ga 0 k) = 0` using `by simp [expOdd, h10.symm]`.

Establish `b4 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expOdd ga 1 k) = ∑ k ∈ Finset.Icc 1 r, (if (1 : ZMod 2) = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga 1 k)`. Simplify using `[expOdd, h10]`. Establish `b1 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expEven n x ga 0 k) ≤ ∑ k ∈ Finset.Icc 1 r, (if (0 : ZMod 2) = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga 0 k) + (n : ℝ) * x`. Establish `: ∑ k ∈ Finset.Icc 1 r, (if k = n then (n : ℝ) * x else 0) ≤ (n : ℝ) * x`. Rewrite using `[Finset.sum_ite_eq']`.

Use `split_ifs`. Conclude with `le_rfl`. Check the signs of the components of the expression. Use `le_trans (le_of_eq ?_) (add_le_add le_rfl this)` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hk : k = n <;> simp [expEven, hk]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deg_le {C : Type} [Field C] {V : VF C} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V 2 I J) (n x r : ℕ) (ga : ZMod 2 → ℕ → ℕ) :
    (RF.monDegAll X 0 (expEven n x ga) r : ℝ) + RF.monDegAll X 0 (expOdd ga) r ≤
      (∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 r, (if s = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k)) + (n : ℝ) * x := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  unfold RF.monDegAll
  rw [sum_two', sum_two', sum_two]
  push_cast
  have a1 := monDeg_le r (X.rkF 0 0) (expEven n x ga 0)
  have a2 := monDeg_le r (X.rkF 0 1) (expEven n x ga 1)
  have a3 := monDeg_le r (X.rkF 0 0) (expOdd ga 0)
  have a4 := monDeg_le r (X.rkF 0 1) (expOdd ga 1)
  have b2 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expEven n x ga 1 k) = 0 := by simp [expEven, h10]
  have b3 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expOdd ga 0 k) = 0 := by simp [expOdd, h10.symm]
  have b4 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expOdd ga 1 k) =
      ∑ k ∈ Finset.Icc 1 r, (if (1 : ZMod 2) = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga 1 k) := by
    simp [expOdd, h10]
  have b1 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expEven n x ga 0 k) ≤
      ∑ k ∈ Finset.Icc 1 r, (if (0 : ZMod 2) = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga 0 k) + (n : ℝ) * x := by
    have : ∑ k ∈ Finset.Icc 1 r, (if k = n then (n : ℝ) * x else 0) ≤ (n : ℝ) * x := by
      rw [Finset.sum_ite_eq']
      split_ifs
      · exact le_rfl
      · positivity
    refine le_trans (le_of_eq ?_) (add_le_add le_rfl this)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = n <;> simp [expEven, hk]
  linarith

/- English proof (translation)
Take `⟨R, alt, gaC, W, nW, T, θ0, rest, ν, hsupp, hmain, hrest, hrows, hD, hval⟩` from `Pk`. Take `⟨C, V, hV, I, J, X, F, hX⟩` from `R`. Simplify using `only at *`. Substitute `hV` using the available equality. Establish `hk : 4 ≤ P.k` using `by have := hP.mk_le; have := hP.m_pos; omega`.

Establish `hl' : (5 : ℝ) ≤ V.l` using `by exact_mod_cast hl`. Establish `h10 : (1 : ZMod 2) ≠ 0` using `by decide`. Establish `hrk` using `fun z => rk_alt (X z) (alt z)`. Establish `hr : P.r = P.k - 1 + P.m` using `hP.r_eq`. Establish `hm : ∀ z, (X z).j + (X z).j' = P.m` using `fun z => (hX z).2`.

Establish `key` using `hval (fun z => [(RF.GlobalTheory.bi 0 0 1 (y z), RF.blockBd V.l (P.k - 1) P.m 1 (y z)), (RF.GlobalTheory.ch 0 0 (u z), RF.chBd V.l (X z).n (X z).m (u z)), (RF.GlobalTheory.mon 0 (expEven (P.k - 1) 0 (gaC z)) P.r, (RF.monDegAll (X z) 0 (expEven (P.k - 1) 0 (gaC z)) P.r : ℝ) / ((V. …`. Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[hrest, Finset.sum_div, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun z _ => ?_` and prove the remaining obligations. Establish `hd` using `deg_le (X z) (P.k - 1) 0 P.r (gaC z)`.

Rewrite `hd` using `[Nat.cast_zero, mul_zero, add_zero]`. Establish `hd'` using `div_le_div_of_nonneg_right hd (c := (V.l : ℝ) - 1) (by linarith)`. Rewrite `hd'` using `[add_div]`. Simplify using `only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, (hX z).1, (hX z).2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `z p hp`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hp`. Break down `hp with rfl | rfl | rfl | rfl` into its components or cases. Conclude with `hy z`. Conclude with `(hC C V 2 (I z) (J z) (X z) (F z) 0 0 (hrk z).1 (u z)).1 (alt z)`.

Conclude with `(hM C V 2 (I z) (J z) (X z) (F z) 0 _ _).1`. Conclude with `(hM C V 2 (I z) (J z) (X z) (F z) 0 _ _).1`. Introduce `z p hp g e M he`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hp`. Break down `hp with rfl | rfl | rfl | rfl` into its components or cases.

Consider the cases of `he`. Consider the cases of `he`. Consider the cases of `he`. Conclude with `⟨0, fun a k ha => by simp [expEven, ha]⟩`. Consider the cases of `he`.

Conclude with `⟨1, fun a k ha => by simp [expOdd, ha]⟩`. Use `le_trans ?_ hrows` and prove the remaining obligations. Establish `: ∀ z : P.Pl, (X z).n + ((X z).n + (P.r + (P.r + 0))) ≤ 4 * P.r`. Introduce `z`. Rewrite using `[(hX z).1]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RF.GlobalTheory.what₂]`. Establish `h2` using `Finset.sum_le_sum (s := Finset.univ) fun z _ => this z`. Rewrite `h2` using `[Finset.sum_const, Finset.card_univ, hP.card, smul_eq_mul]`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `z s k`. Establish `e0` using `(hrk z).2.1`. Establish `e1` using `(hrk z).2.2`. Establish `hn` using `(hX z).1`. Establish `hmz` using `hm z`.

Establish `hs` using `hsupp z s k`. Establish `hw` using `hW z`. Establish `hma` using `hmain z`. Establish `hs2 : s = 0 ∨ s = 1` using `(by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) s`. Establish `h11 : (1 : ZMod 2) + 1 = 0` using `by decide`.

Simplify using `only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RF.GlobalTheory.wt, hn]`. Break down `hs2 with rfl | rfl` into its components or cases. Establish `hmin : min P.r ((X z).rkF 0 0) = (X z).rkF 0 0` using `min_eq_right (by omega)`. Distinguish the cases in `hkn : k = P.k - 1`. Substitute `hkn` using the available equality.

Establish `c1 : 1 ≤ P.k - 1` using `by omega`. Establish `c2 : P.k - 1 ≤ (X z).rkF 0 0` using `by omega`. Simplify using `[expEven, expOdd, hmin, c1, c2, hma, hw, h10.symm]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hg : gaC z 0 k = 0`.

Simplify using `[expEven, expOdd, hkn, hg, h10.symm]`. Simplify using `[expEven, expOdd, hkn, hmin, hs hg, h10.symm]`. Establish `hmin : min P.r ((X z).rkF 0 1) = (X z).rkF 0 1` using `min_eq_right (by omega)`. Distinguish the cases in `hg : gaC z 1 k = 0`. Simplify using `[expEven, expOdd, hg, h10, h11, h10.symm]`.

Simplify using `[expEven, expOdd, hmin, hs hg, h10, h11, h10.symm]`.
-/
theorem val_le (hC : RF.CHSupply) (hM : RF.MONSupply) (C1 : ℝ) (P : RF.Par) (l : ℕ) (hP : ParOK P) (hl : 5 ≤ l)
    (Pk : RF.PkgPhiC P l C1) (y u : P.Pl → ℕ) (hW : ∀ z, Pk.W z = (l + 1) * y z + u z)
    (hy : ∀ z, (RF.GlobalTheory.bi 0 0 1 (y z)).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m 1 (y z))) :
    Pk.ν ≤ ∑ z, (RF.blockBd l (P.k - 1) P.m 1 (y z) + RF.chBd l (P.k - 1) P.m (u z)) + Pk.rest / ((l : ℝ) - 1) := by
  obtain ⟨R, alt, gaC, W, nW, T, θ0, rest, ν, hsupp, hmain, hrest, hrows, hD, hval⟩ := Pk
  obtain ⟨C, V, hV, I, J, X, F, hX⟩ := R
  dsimp only at *
  subst hV
  have hk : 4 ≤ P.k := by have := hP.mk_le; have := hP.m_pos; omega
  have hl' : (5 : ℝ) ≤ V.l := by exact_mod_cast hl
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hrk := fun z => rk_alt (X z) (alt z)
  have hr : P.r = P.k - 1 + P.m := hP.r_eq
  have hm : ∀ z, (X z).j + (X z).j' = P.m := fun z => (hX z).2
  have key := hval (fun z =>
    [(RF.GlobalTheory.bi 0 0 1 (y z), RF.blockBd V.l (P.k - 1) P.m 1 (y z)),
     (RF.GlobalTheory.ch 0 0 (u z), RF.chBd V.l (X z).n (X z).m (u z)),
     (RF.GlobalTheory.mon 0 (expEven (P.k - 1) 0 (gaC z)) P.r,
       (RF.monDegAll (X z) 0 (expEven (P.k - 1) 0 (gaC z)) P.r : ℝ) / ((V.l : ℝ) - 1)),
     (RF.GlobalTheory.mon 0 (expOdd (gaC z)) P.r,
       (RF.monDegAll (X z) 0 (expOdd (gaC z)) P.r : ℝ) / ((V.l : ℝ) - 1))]) ?_ ?_ ?_ ?_
  · refine key.trans ?_
    rw [hrest, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    have hd := deg_le (X z) (P.k - 1) 0 P.r (gaC z)
    rw [Nat.cast_zero, mul_zero, add_zero] at hd
    have hd' := div_le_div_of_nonneg_right hd (c := (V.l : ℝ) - 1) (by linarith)
    rw [add_div] at hd'
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, (hX z).1, (hX z).2]
    linarith
  · intro z p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hy z
    · exact (hC C V 2 (I z) (J z) (X z) (F z) 0 0 (hrk z).1 (u z)).1 (alt z)
    · exact (hM C V 2 (I z) (J z) (X z) (F z) 0 _ _).1
    · exact (hM C V 2 (I z) (J z) (X z) (F z) 0 _ _).1
  · intro z p hp g e M he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · cases he
    · cases he
    · cases he
      exact ⟨0, fun a k ha => by simp [expEven, ha]⟩
    · cases he
      exact ⟨1, fun a k ha => by simp [expOdd, ha]⟩
  · refine le_trans ?_ hrows
    have : ∀ z : P.Pl, (X z).n + ((X z).n + (P.r + (P.r + 0))) ≤ 4 * P.r := by
      intro z; rw [(hX z).1]; omega
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RF.GlobalTheory.what₂]
    have h2 := Finset.sum_le_sum (s := Finset.univ) fun z _ => this z
    rw [Finset.sum_const, Finset.card_univ, hP.card, smul_eq_mul] at h2
    nlinarith
  · intro z s k
    have e0 := (hrk z).2.1
    have e1 := (hrk z).2.2
    have hn := (hX z).1
    have hmz := hm z
    have hs := hsupp z s k
    have hw := hW z
    have hma := hmain z
    have hs2 : s = 0 ∨ s = 1 := (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) s
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RF.GlobalTheory.wt, hn]
    rcases hs2 with rfl | rfl
    · have hmin : min P.r ((X z).rkF 0 0) = (X z).rkF 0 0 := min_eq_right (by omega)
      by_cases hkn : k = P.k - 1
      · subst hkn
        have c1 : 1 ≤ P.k - 1 := by omega
        have c2 : P.k - 1 ≤ (X z).rkF 0 0 := by omega
        simp [expEven, expOdd, hmin, c1, c2, hma, hw, h10.symm]
        ring
      · by_cases hg : gaC z 0 k = 0
        · simp [expEven, expOdd, hkn, hg, h10.symm]
        · simp [expEven, expOdd, hkn, hmin, hs hg, h10.symm]
    · have hmin : min P.r ((X z).rkF 0 1) = (X z).rkF 0 1 := min_eq_right (by omega)
      by_cases hg : gaC z 1 k = 0
      · simp [expEven, expOdd, hg, h10, h11, h10.symm]
      · simp [expEven, expOdd, hmin, hs hg, h10, h11, h10.symm]

/- English proof (translation)
Introduce `C1 hC1`. Use `⟨900 + 7 * C1, by linarith, fun P l hP hp hl Pk => ?_⟩` and prove the remaining obligations. Establish `hk : 4 ≤ P.k` using `by have := hP.mk_le; have := hP.m_pos; omega`. Establish `hG : ∀ z, RF.Windows (S0 l 1 (P.k - 1)) {y | (RF.GlobalTheory.bi 0 0 1 y).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m 1 y)}`. Introduce `z`.

Use `hB Pk.R.C Pk.R.V 2 (Pk.R.I z) (Pk.R.J z) (Pk.R.X z) (Pk.R.F z) (Pk.alt z) (by rw [Pk.R.hVl]; exact hl) (by rw [(Pk.R.hn z).1]; omega) 0 0 (rk_alt _ (Pk.alt z)).1 1 odd_one (by norm_num)` as an intermediate fact. Rewrite `this` using `[(Pk.R.hn z).1, (Pk.R.hn z).2, Pk.R.hVl]`. Then use the resulting hypothesis. Use `choose y u hW hy hu using fun z => exists_good l _ (Pk.W z) _ (hG z)`. Establish `h1` using `val_le hC hM C1 P l hP hl Pk y u hW hy`. Establish `hD` using `Pk.deg`.

Generalize the expression as in `Pk.T = T at *`. Generalize the expression as in `Pk.ν = ν at *`. Generalize the expression as in `Pk.rest = rest at *`. Generalize the expression as in `Pk.W = W at *`. Use `clear hG hy`.

Take `⟨n, hn⟩ : ∃ n, P.k = n + 1` from `⟨P.k - 1, by omega⟩`. Establish `hn3 : 3 ≤ n` using `by omega`. Establish `hn1 : P.k - 1 = n` using `by omega`. Establish `hkr : (P.k : ℝ) = n + 1` using `by exact_mod_cast hn`. Establish `hl' : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`.

Establish `hn' : (3 : ℝ) ≤ n` using `by exact_mod_cast hn3`. Establish `hmn : (P.m : ℝ) ≤ n` using `by have := hP.mk_le; exact_mod_cast (by omega : P.m ≤ n)`. Rewrite `h1`, `hu` using `[hn1]`. Establish `hT : 0 < T` using `by linarith [hD.T_one]`. Establish `hSE` using `hP.SE_nonneg`.

Establish `hl2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hrho : 0 ≤ Formalism.IncomingBounds.rho l`. Unfold `Formalism.IncomingBounds.rho`. Check the signs of the components of the expression. Establish `hrho' : Formalism.IncomingBounds.rho l ≤ 1 / l`.

Unfold `Formalism.IncomingBounds.rho`. Apply `one_div_le_one_div_of_le (by linarith); nlinarith` to reduce the goal to its premises. Use `set L := Real.log ((n : ℝ) + 1) with hLdef`. Establish `hL : 1 ≤ L` using `one_le_log _ (by linarith)`. Establish `h2 : ∀ z, T * (RF.blockBd l n P.m 1 (y z) + RF.chBd l n P.m (u z)) ≤ Formalism.IncomingBounds.rho l * (n * P.w z) + 4 * P.m * P.w z / l + 5 * C1 * ((n + 1) * P.SE / l) + T * (900 * ((n : ℝ) ^ 3 * L))`.

Introduce `z`. Establish `a1` using `place_bound l n P.m _ (y z) (u z) hl (by omega) (hu z)`. Rewrite `a1` using `[← hW z]`. Establish `a2` using `additive_bound l n hl hn3`. Establish `a3` using `hD.TW_hi z`.

Establish `a4 : 0 ≤ Formalism.IncomingBounds.rho l * n + 4 * P.m / l` using `by positivity`. Establish `a5 : Formalism.IncomingBounds.rho l * n + 4 * P.m / l ≤ 5 * (n + 1) / l`. Establish `b1 : Formalism.IncomingBounds.rho l * n ≤ 1 / l * (n + 1)` using `by gcongr; linarith`. Establish `b2 : (4 : ℝ) * P.m / l ≤ 4 * (n + 1) / l` using `by gcongr; linarith`. Combine the equalities or inequalities in the displayed calculation.

Establish `a6` using `mul_le_mul_of_nonneg_right a5 (mul_nonneg hC1 hSE)`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : T * ∑ z, (RF.blockBd l n P.m 1 (y z) + RF.chBd l n P.m (u z)) ≤ n * (∑ z, P.w z) / ((l : ℝ) ^ 2 - 1) + 4 * (P.m * (∑ z, P.w z) / l) + 5 * C1 * (P.f * (n + 1) * P.SE / l) + 900 * (T * P.f * (n : ℝ) ^ 3 * L)`. Rewrite using `[Finset.mul_sum]`. Use `(Finset.sum_le_sum fun z _ => h2 z).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_univ, hP.card, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum, nsmul_eq_mul, nsmul_eq_mul]`. Unfold `Formalism.IncomingBounds.rho`. Expand and normalize the polynomial expressions, which then agree. Establish `hw : 0 ≤ ∑ z, P.w z` using `Finset.sum_nonneg fun z _ => (hD.w_pos z).le`. Establish `h4 : T * (rest / ((l : ℝ) - 1)) ≤ 2 * C1 * (P.f * (n + 1) * P.SE / l)`.

Establish `hi : 1 / ((l : ℝ) - 1) ≤ 2 / l`. Rewrite using `[div_le_div_iff₀ (by linarith) (by linarith)]; linarith`. Establish `h1l : 0 ≤ 1 / ((l : ℝ) - 1)` using `div_nonneg zero_le_one (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Establish `h8` using `mul_le_mul_of_nonneg_left h1 hT.le`.

Rewrite `h8` using `[mul_add]`. Establish `hth` using `thl_nonneg P.k l`. Unfold `errB`. Rewrite using `[hkr, ← hLdef, add_sub_cancel_right]`. Establish `eA : L * P.m * (∑ z, P.w z) / l = L * (P.m * (∑ z, P.w z) / l)` using `by ring`.

Establish `eD : T * P.f * (n : ℝ) ^ 3 * L ^ 2 = L * (T * P.f * (n : ℝ) ^ 3 * L)` using `by ring`. Rewrite using `[eA, eD]`. Establish `pA : 0 ≤ P.m * (∑ z, P.w z) / l` using `by positivity`. Establish `pB : 0 ≤ P.f * ((n : ℝ) + 1) * P.SE / l` using `by positivity`. Establish `pC : 0 ≤ ((n : ℝ) + 1) * thl P.k l * ∑ z, P.w z` using `by positivity`.

Establish `pD : 0 ≤ T * P.f * (n : ℝ) ^ 3 * L` using `by positivity`. Generalize the expression as in `P.m * (∑ z, P.w z) / l = A at *`. Generalize the expression as in `P.f * ((n : ℝ) + 1) * P.SE / l = B at *`. Generalize the expression as in `((n : ℝ) + 1) * thl P.k l * ∑ z, P.w z = Cth at *`. Generalize the expression as in `T * P.f * (n : ℝ) ^ 3 * L = D at *`.

Establish `qA : A ≤ L * A` using `le_mul_of_one_le_left pA hL`. Establish `qD : D ≤ L * D` using `le_mul_of_one_le_left pD hL`. Establish `r1 : 0 ≤ C1 * (L * A + Cth + L * D)` using `mul_nonneg hC1 (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem of_supplies (hB : RF.BiSupply) (hC : RF.CHSupply) (hM : RF.MONSupply) : PhiCBd := by
  intro C1 hC1
  refine ⟨900 + 7 * C1, by linarith, fun P l hP hp hl Pk => ?_⟩
  have hk : 4 ≤ P.k := by have := hP.mk_le; have := hP.m_pos; omega
  have hG : ∀ z, RF.Windows (S0 l 1 (P.k - 1)) {y | (RF.GlobalTheory.bi 0 0 1 y).Attains (Pk.R.X z) (Pk.R.F z)
      (RF.blockBd l (P.k - 1) P.m 1 y)} := by
    intro z
    have := hB Pk.R.C Pk.R.V 2 (Pk.R.I z) (Pk.R.J z) (Pk.R.X z) (Pk.R.F z) (Pk.alt z) (by rw [Pk.R.hVl]; exact hl)
      (by rw [(Pk.R.hn z).1]; omega) 0 0 (rk_alt _ (Pk.alt z)).1 1 odd_one (by norm_num)
    rwa [(Pk.R.hn z).1, (Pk.R.hn z).2, Pk.R.hVl] at this
  choose y u hW hy hu using fun z => exists_good l _ (Pk.W z) _ (hG z)
  have h1 := val_le hC hM C1 P l hP hl Pk y u hW hy
  have hD := Pk.deg
  generalize Pk.T = T at *
  generalize Pk.ν = ν at *
  generalize Pk.rest = rest at *
  generalize Pk.W = W at *
  clear hG hy
  obtain ⟨n, hn⟩ : ∃ n, P.k = n + 1 := ⟨P.k - 1, by omega⟩
  have hn3 : 3 ≤ n := by omega
  have hn1 : P.k - 1 = n := by omega
  have hkr : (P.k : ℝ) = n + 1 := by exact_mod_cast hn
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hmn : (P.m : ℝ) ≤ n := by have := hP.mk_le; exact_mod_cast (by omega : P.m ≤ n)
  rw [hn1] at h1 hu
  have hT : 0 < T := by linarith [hD.T_one]
  have hSE := hP.SE_nonneg
  have hl2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hrho : 0 ≤ Formalism.IncomingBounds.rho l := by
    unfold Formalism.IncomingBounds.rho; positivity
  have hrho' : Formalism.IncomingBounds.rho l ≤ 1 / l := by
    unfold Formalism.IncomingBounds.rho
    apply one_div_le_one_div_of_le (by linarith); nlinarith
  set L := Real.log ((n : ℝ) + 1) with hLdef
  have hL : 1 ≤ L := one_le_log _ (by linarith)
  have h2 : ∀ z, T * (RF.blockBd l n P.m 1 (y z) + RF.chBd l n P.m (u z)) ≤
      Formalism.IncomingBounds.rho l * (n * P.w z) + 4 * P.m * P.w z / l + 5 * C1 * ((n + 1) * P.SE / l) +
        T * (900 * ((n : ℝ) ^ 3 * L)) := by
    intro z
    have a1 := place_bound l n P.m _ (y z) (u z) hl (by omega) (hu z)
    rw [← hW z] at a1
    have a2 := additive_bound l n hl hn3
    have a3 := hD.TW_hi z
    have a4 : 0 ≤ Formalism.IncomingBounds.rho l * n + 4 * P.m / l := by positivity
    have a5 : Formalism.IncomingBounds.rho l * n + 4 * P.m / l ≤ 5 * (n + 1) / l := by
      have b1 : Formalism.IncomingBounds.rho l * n ≤ 1 / l * (n + 1) := by gcongr; linarith
      have b2 : (4 : ℝ) * P.m / l ≤ 4 * (n + 1) / l := by gcongr; linarith
      calc _ ≤ 1 / l * (n + 1) + 4 * ((n : ℝ) + 1) / l := add_le_add b1 b2
        _ = _ := by ring
    have a6 := mul_le_mul_of_nonneg_right a5 (mul_nonneg hC1 hSE)
    calc _ ≤ T * (Formalism.IncomingBounds.rho l * n * (W z : ℝ) + 4 * P.m * (W z : ℝ) / l + 900 * ((n : ℝ) ^ 3 * L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hT.le
      _ = (Formalism.IncomingBounds.rho l * n + 4 * P.m / l) * (T * W z) + T * (900 * ((n : ℝ) ^ 3 * L)) := by ring
      _ ≤ (Formalism.IncomingBounds.rho l * n + 4 * P.m / l) * (P.w z + C1 * P.SE) + T * (900 * ((n : ℝ) ^ 3 * L)) := by
          gcongr
      _ = Formalism.IncomingBounds.rho l * (n * P.w z) + 4 * P.m * P.w z / l + (Formalism.IncomingBounds.rho l * n + 4 * P.m / l) * (C1 * P.SE) +
          T * (900 * ((n : ℝ) ^ 3 * L)) := by ring
      _ ≤ Formalism.IncomingBounds.rho l * (n * P.w z) + 4 * P.m * P.w z / l + (5 * (n + 1) / l) * (C1 * P.SE) +
          T * (900 * ((n : ℝ) ^ 3 * L)) := by linarith
      _ = _ := by ring
  have h3 : T * ∑ z, (RF.blockBd l n P.m 1 (y z) + RF.chBd l n P.m (u z)) ≤
      n * (∑ z, P.w z) / ((l : ℝ) ^ 2 - 1) + 4 * (P.m * (∑ z, P.w z) / l) + 5 * C1 * (P.f * (n + 1) * P.SE / l) +
        900 * (T * P.f * (n : ℝ) ^ 3 * L) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun z _ => h2 z).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, hP.card, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum,
      nsmul_eq_mul, nsmul_eq_mul]
    unfold Formalism.IncomingBounds.rho
    ring
  have hw : 0 ≤ ∑ z, P.w z := Finset.sum_nonneg fun z _ => (hD.w_pos z).le
  have h4 : T * (rest / ((l : ℝ) - 1)) ≤ 2 * C1 * (P.f * (n + 1) * P.SE / l) := by
    have hi : 1 / ((l : ℝ) - 1) ≤ 2 / l := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    have h1l : 0 ≤ 1 / ((l : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    calc T * (rest / ((l : ℝ) - 1)) = T * rest * (1 / ((l : ℝ) - 1)) := by ring
      _ ≤ C1 * (P.f * P.k * P.SE) * (2 / l) :=
          mul_le_mul hD.rest_le hi h1l (by positivity)
      _ = _ := by rw [hkr]; ring
  have h8 := mul_le_mul_of_nonneg_left h1 hT.le
  rw [mul_add] at h8
  have hth := thl_nonneg P.k l
  unfold errB
  rw [hkr, ← hLdef, add_sub_cancel_right]
  have eA : L * P.m * (∑ z, P.w z) / l = L * (P.m * (∑ z, P.w z) / l) := by ring
  have eD : T * P.f * (n : ℝ) ^ 3 * L ^ 2 = L * (T * P.f * (n : ℝ) ^ 3 * L) := by ring
  rw [eA, eD]
  have pA : 0 ≤ P.m * (∑ z, P.w z) / l := by positivity
  have pB : 0 ≤ P.f * ((n : ℝ) + 1) * P.SE / l := by positivity
  have pC : 0 ≤ ((n : ℝ) + 1) * thl P.k l * ∑ z, P.w z := by positivity
  have pD : 0 ≤ T * P.f * (n : ℝ) ^ 3 * L := by positivity
  generalize P.m * (∑ z, P.w z) / l = A at *
  generalize P.f * ((n : ℝ) + 1) * P.SE / l = B at *
  generalize ((n : ℝ) + 1) * thl P.k l * ∑ z, P.w z = Cth at *
  generalize T * P.f * (n : ℝ) ^ 3 * L = D at *
  have qA : A ≤ L * A := le_mul_of_one_le_left pA hL
  have qD : D ≤ L * D := le_mul_of_one_le_left pD hL
  have r1 : 0 ≤ C1 * (L * A + Cth + L * D) := mul_nonneg hC1 (by linarith)
  nlinarith

/- English proof (translation)
The claim follows from `of_supplies GlobalTheory.T.oddLevelBlock_bound_attained.2 GlobalTheory.CharBlock.chSupply.2 GlobalTheory.T.monomialBlock_supply_both_typings.2`.
-/
theorem phiCBd : PhiCBd := of_supplies GlobalTheory.T.oddLevelBlock_bound_attained.2 GlobalTheory.CharBlock.chSupply.2 GlobalTheory.T.monomialBlock_supply_both_typings.2

end GlobalTheory.GoodDepth.ConjPkg
