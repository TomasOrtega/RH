import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet

noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.HarmCone

variable {n : ℕ}

def sg (lev : Fin n → ℕ) (a b : Fin n) : ℝ :=
  (if lev a < lev b then 1 else 0) - (if lev b < lev a then 1 else 0)

/- English proof (translation)
Simplify using `only [rhoU, sg, Finset.sum_sub_distrib, Finset.sum_boole]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_rhoU (lev : Fin n → ℕ) (a : Fin n) : 2 * rhoU lev a = ∑ b, sg lev a b := by
  simp only [rhoU, sg, Finset.sum_sub_distrib, Finset.sum_boole]
  ring

/- English proof (translation)
Unfold `sg`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sg_anti (lev : Fin n → ℕ) (a b : Fin n) : sg lev a b = - sg lev b a := by
  unfold sg
  ring

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sg_cases (lev : Fin n → ℕ) (a b : Fin n) :
    sg lev a b = 1 ∨ sg lev a b = 0 ∨ sg lev a b = -1 := by
  unfold sg
  split_ifs <;> norm_num

/- English proof (translation)
Break down `lt_trichotomy (lev a) (lev b) with h | h | h` into its components or cases. Establish `h' : (lev a : ℝ) < lev b` using `by exact_mod_cast h`. Establish `hs : sg lev a b = 1`. Unfold `sg`. Rewrite using `[if_pos h, if_neg (by omega)]`.

Evaluate the numerical expressions. Rewrite using `[hs, abs_of_neg (by linarith)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : sg lev a b = 0`. Unfold `sg`.

Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Evaluate the numerical expressions. Rewrite using `[hs, h]`. Simplify using the standard rewrite rules. Establish `h' : (lev b : ℝ) < lev a` using `by exact_mod_cast h`.

Establish `hs : sg lev a b = -1`. Unfold `sg`. Rewrite using `[if_neg (by omega), if_pos h]`. Evaluate the numerical expressions. Rewrite using `[hs, abs_of_pos (by linarith)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_sg_self (lev : Fin n → ℕ) (a b : Fin n) :
    ((lev a : ℝ) - lev b) * sg lev a b = -|(lev a : ℝ) - lev b| := by
  rcases lt_trichotomy (lev a) (lev b) with h | h | h
  · have h' : (lev a : ℝ) < lev b := by exact_mod_cast h
    have hs : sg lev a b = 1 := by
      unfold sg
      rw [if_pos h, if_neg (by omega)]
      norm_num
    rw [hs, abs_of_neg (by linarith)]
    ring
  · have hs : sg lev a b = 0 := by
      unfold sg
      rw [if_neg (by omega), if_neg (by omega)]
      norm_num
    rw [hs, h]
    simp
  · have h' : (lev b : ℝ) < lev a := by exact_mod_cast h
    have hs : sg lev a b = -1 := by
      unfold sg
      rw [if_neg (by omega), if_pos h]
      norm_num
    rw [hs, abs_of_pos (by linarith)]
    ring

/- English proof (translation)
Establish `h1` using `neg_abs_le x`. Establish `h2` using `le_abs_self x`. Establish `h3` using `abs_nonneg x`. Apply the tactic sequence `rcases sg_cases lev a b with h | h | h <;> rw [h] <;> linarith`.
-/
theorem neg_abs_le_mul_sg (lev : Fin n → ℕ) (x : ℝ) (a b : Fin n) : -|x| ≤ x * sg lev a b := by
  have h1 := neg_abs_le x
  have h2 := le_abs_self x
  have h3 := abs_nonneg x
  rcases sg_cases lev a b with h | h | h <;> rw [h] <;> linarith

/- English proof (translation)
Simplify using `[mul_sub, Finset.sum_sub_distrib]`.
-/
theorem pair_root (f : Fin n → ℝ) (a b : Fin n) :
    ∑ x, f x * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) = f a - f b := by
  simp [mul_sub, Finset.sum_sub_distrib]

def dsg (lev lev' : Fin n → ℕ) (x b : Fin n) : ℝ := sg lev' x b - sg lev x b

/- English proof (translation)
Unfold `dsg`. Rewrite using `[sg_anti lev' x b, sg_anti lev x b]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dsg_anti (lev lev' : Fin n → ℕ) (x b : Fin n) : dsg lev lev' x b = - dsg lev lev' b x := by
  unfold dsg
  rw [sg_anti lev' x b, sg_anti lev x b]
  ring

/- English proof (translation)
Unfold `dsg`. Rewrite using `[mul_sub, mul_sg_self]`. Use `neg_abs_le_mul_sg lev' ((lev x : ℝ) - lev b) x b` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dsg_nonneg (lev lev' : Fin n → ℕ) (x b : Fin n) :
    0 ≤ ((lev x : ℝ) - lev b) * dsg lev lev' x b := by
  unfold dsg
  rw [mul_sub, mul_sg_self]
  have := neg_abs_le_mul_sg lev' ((lev x : ℝ) - lev b) x b
  linarith

/- English proof (translation)
Establish `e1 : ∑ x, ∑ b, (lev x : ℝ) * dsg lev lev' x b = ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b`. Simplify using `only [Finset.mul_sum]`. Establish `e2 : ∑ x, ∑ b, (lev b : ℝ) * dsg lev lev' x b = -∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b`. Rewrite using `[Finset.sum_comm, ← e1, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[dsg_anti lev lev' b x]`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b = 2 * ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b`.

Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : 0 ≤ ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b` using `Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun b _ => dsg_nonneg lev lev' x b`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pairing_nonneg (lev lev' : Fin n → ℕ) :
    0 ≤ ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
  have e1 : ∑ x, ∑ b, (lev x : ℝ) * dsg lev lev' x b = ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [Finset.mul_sum]
  have e2 : ∑ x, ∑ b, (lev b : ℝ) * dsg lev lev' x b = -∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    rw [Finset.sum_comm, ← e1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dsg_anti lev lev' b x]
    ring
  have e3 : ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b
      = 2 * ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e1, e2]
    ring
  have e4 : 0 ≤ ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun b _ => dsg_nonneg lev lev' x b
  linarith

/- English proof (translation)
Introduce `n lam _ lev lev' _ _ hc`. Take `⟨c, hc0, hQ⟩` from `hc`. Establish `hQx : ∀ x, (muQ lam lev' - muQ lam lev) x = ∑ b, dsg lev lev' x b`. Introduce `x`. Simplify using `only [Pi.sub_apply, muQ, dsg, Finset.sum_sub_distrib, ← two_rhoU]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hD : ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b = ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b)`. Establish `e : ∀ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b = ∑ a, ∑ b, (c a b : ℝ) * ((lev x : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)))`. Introduce `x`. Rewrite using `[← hQx, hQ x, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, pair_root (fun x => (lev x : ℝ)) a b]`.

Establish `hterm : ∀ a b, (c a b : ℝ) * ((lev a : ℝ) - lev b) ≤ 0`. Introduce `a b`. Distinguish the cases in `h0 : c a b = 0`. Simplify using `[h0]`. Establish `h1 : (lev a : ℝ) < lev b` using `by exact_mod_cast hc0 a b h0`.

Establish `h2 : (0 : ℝ) ≤ c a b` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsum : ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) = 0` using `le_antisymm (Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => hterm a b) (hD ▸ pairing_nonneg lev lev')`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ => hterm a b)).1 hsum`. Establish `hz : ∀ a b, c a b = 0`.

Introduce `a b`. Assume the negation of the conclusion as `h0`. Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hterm a b)).1 (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)`. Establish `h3 : (lev a : ℝ) < lev b` using `by exact_mod_cast hc0 a b h0`. Establish `h4 : (c a b : ℝ) ≠ 0` using `by exact_mod_cast h0`.

Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `h4 h`. Combine the linear equalities and inequalities to obtain the conclusion. Use function extensionality and compare the values at `x`. Establish `h5` using `hQ x`.

Simplify using `only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at h5`. Conclude with `sub_eq_zero.1 h5`.
-/
theorem harm_cone : N1 := by
  intro n lam _ lev lev' _ _ hc
  obtain ⟨c, hc0, hQ⟩ := hc
  have hQx : ∀ x, (muQ lam lev' - muQ lam lev) x = ∑ b, dsg lev lev' x b := by
    intro x
    simp only [Pi.sub_apply, muQ, dsg, Finset.sum_sub_distrib, ← two_rhoU]
    ring
  have hD : ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b
      = ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) := by
    have e : ∀ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b = ∑ a, ∑ b, (c a b : ℝ) *
        ((lev x : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))) := by
      intro x
      rw [← hQx, hQ x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, pair_root (fun x => (lev x : ℝ)) a b]
  have hterm : ∀ a b, (c a b : ℝ) * ((lev a : ℝ) - lev b) ≤ 0 := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have h1 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
      have h2 : (0 : ℝ) ≤ c a b := Nat.cast_nonneg _
      nlinarith
  have hsum : ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) = 0 :=
    le_antisymm (Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => hterm a b)
      (hD ▸ pairing_nonneg lev lev')
  have h1 := (Finset.sum_eq_zero_iff_of_nonpos
    (fun a _ => Finset.sum_nonpos fun b _ => hterm a b)).1 hsum
  have hz : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hterm a b)).1
      (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)
    have h3 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
    have h4 : (c a b : ℝ) ≠ 0 := by exact_mod_cast h0
    rcases mul_eq_zero.1 h2 with h | h
    · exact h4 h
    · linarith
  funext x
  have h5 := hQ x
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at h5
  exact sub_eq_zero.1 h5

end GlobalTheory.CompanionTheory.HarmCone
