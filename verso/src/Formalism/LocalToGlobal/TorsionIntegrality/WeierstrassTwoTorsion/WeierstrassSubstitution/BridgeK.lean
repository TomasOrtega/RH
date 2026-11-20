import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

/- English proof (translation)
Unfold `ShortInv`. Introduce `K _ _ g2 g3`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [shortW, WeierstrassCurve.b₂]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `g₂`. Simplify using `only [shortW, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]`. Expand and normalize the polynomial expressions, which then agree. Unfold `g₃`. Simplify using `only [shortW, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem short_weierstrass_inverse : ShortInv := by
  unfold ShortInv
  intro K _ _ g2 g3
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [shortW, WeierstrassCurve.b₂]
    ring
  · unfold g₂
    simp only [shortW, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  · unfold g₃
    simp only [shortW, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    ring
  · simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring

namespace BridgeK

open Formalism.L2.Th1.CM

/- English proof (translation)
Use `conv_lhs => unfold cW`. Rewrite using `[Nat.strongRecOn_eq]`. Simplify using `only [dite_eq_ite]`. Both sides reduce to the same expression.
-/
theorem cW_eq {K : Type} [Field K] (g2 g3 : K) (k : ℕ) :
    cW g2 g3 k = if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
      if 4 ≤ k then
        3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
          ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
      else 0 := by
  conv_lhs => unfold cW
  rw [Nat.strongRecOn_eq]
  simp only [dite_eq_ite]
  rfl

/- English proof (translation)
Rewrite using `[cW_eq]`. Simplify using the standard rewrite rules.
-/
theorem cW_zero {K : Type} [Field K] (g2 g3 : K) : cW g2 g3 0 = 0 := by
  rw [cW_eq]
  simp

/- English proof (translation)
Take `⟨_, h0, _, h2, h4⟩` from `hS K W`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Break down `Nat.lt_or_ge k 3 with hk | hk` into its components or cases. Use `interval_cases k`.

Rewrite using `[cW_eq]`. Simplify using `[h0]`. Rewrite using `[cW_eq]`. Simplify using `[h2]`. Rewrite using `[cW_eq]`.

Simplify using `[h4]`. Establish `hrec` using `hR K W k hk`. Rewrite using `[cW_eq, if_neg (show k + 1 ≠ 2 by omega), if_neg (show k + 1 ≠ 3 by omega), if_pos (show 4 ≤ k + 1 by omega)]`. Establish `hsum : (∑ m : Fin (k + 1 - 3), cW (g₂ W) (g₃ W) (m.val + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m.val + 2))) = ∑ i ∈ Finset.Icc 1 (k - 2), coeff (2 * i) (wpReg W) * coeff (2 * (k - 1 - i)) (wpReg W)`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun m => cW (g₂ W) (g₃ W) (m + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m + 2))) (k + 1 - 3)]`.

Use `Finset.sum_nbij' (fun m => m + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Rewrite `ha` using `[Finset.mem_range]`. Rewrite using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.

Introduce `a ha`. Rewrite `ha` using `[Finset.mem_Icc]`. Rewrite using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Introduce `a _ show a + 1 - 1 = a`.

Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Rewrite `ha` using `[Finset.mem_Icc]`. Use `show a - 1 + 1 = a`. Use linear arithmetic over natural numbers and integers.

Introduce `m hm`. Rewrite `hm` using `[Finset.mem_range]`. Use `show cW (g₂ W) (g₃ W) (m + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m + 2)) = coeff (2 * (m + 1)) (wpReg W) * coeff (2 * (k - 1 - (m + 1))) (wpReg W)`. Rewrite using `[show m + 2 = m + 1 + 1 by omega, show k + 1 - (m + 1 + 1) = k - 2 - m + 1 by omega, ih (m + 1) (by omega), ih (k - 2 - m) (by omega), show k - 1 - (m + 1) = k - 2 - m by omega]`. Rewrite using `[hsum]`.

Establish `hne1 : (2 * ((k : K) + 1) + 1) ≠ 0`. Establish `e : ((2 * k + 3 : ℕ) : K) = 2 * ((k : K) + 1) + 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e]`.

Conclude with `(show 2 * k + 3 ≠ 0 by omega)` after adjusting the coercions. Establish `hne2 : ((k : K) + 1 - 3) ≠ 0`. Establish `e : ((k - 2 : ℕ) : K) = (k : K) + 1 - 3`. Move the coercions through the operations in `[Nat.cast_sub (show 2 ≤ k by omega)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← e]`. Conclude with `(show k - 2 ≠ 0 by omega)` after adjusting the coercions. Use `push_cast`. Rewrite using `[div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hne1 hne2)]`. Take the linear combination `-hrec`.
-/
theorem cW_succ (hS : WpShape.{0}) (hR : WpRecursion.{0}) {K : Type} [Field K] [CharZero K]
    (W : WeierstrassCurve K) (k : ℕ) :
    cW (g₂ W) (g₃ W) (k + 1) = coeff (2 * k) (wpReg W) := by
  obtain ⟨_, h0, _, h2, h4⟩ := hS K W
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · rw [cW_eq]
        simp [h0]
      · rw [cW_eq]
        simp [h2]
      · rw [cW_eq]
        simp [h4]
    · have hrec := hR K W k hk
      rw [cW_eq, if_neg (show k + 1 ≠ 2 by omega), if_neg (show k + 1 ≠ 3 by omega),
        if_pos (show 4 ≤ k + 1 by omega)]
      have hsum : (∑ m : Fin (k + 1 - 3), cW (g₂ W) (g₃ W) (m.val + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m.val + 2)))
          = ∑ i ∈ Finset.Icc 1 (k - 2), coeff (2 * i) (wpReg W) * coeff (2 * (k - 1 - i)) (wpReg W) := by
        rw [Fin.sum_univ_eq_sum_range (fun m => cW (g₂ W) (g₃ W) (m + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m + 2)))
          (k + 1 - 3)]
        refine Finset.sum_nbij' (fun m => m + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
        · intro a ha
          rw [Finset.mem_range] at ha
          rw [Finset.mem_Icc]
          omega
        · intro a ha
          rw [Finset.mem_Icc] at ha
          rw [Finset.mem_range]
          omega
        · intro a _
          show a + 1 - 1 = a
          omega
        · intro a ha
          rw [Finset.mem_Icc] at ha
          show a - 1 + 1 = a
          omega
        · intro m hm
          rw [Finset.mem_range] at hm
          show cW (g₂ W) (g₃ W) (m + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m + 2))
            = coeff (2 * (m + 1)) (wpReg W) * coeff (2 * (k - 1 - (m + 1))) (wpReg W)
          rw [show m + 2 = m + 1 + 1 by omega, show k + 1 - (m + 1 + 1) = k - 2 - m + 1 by omega,
            ih (m + 1) (by omega), ih (k - 2 - m) (by omega), show k - 1 - (m + 1) = k - 2 - m by omega]
      rw [hsum]
      have hne1 : (2 * ((k : K) + 1) + 1) ≠ 0 := by
        have e : ((2 * k + 3 : ℕ) : K) = 2 * ((k : K) + 1) + 1 := by
          push_cast
          ring
        rw [← e]
        exact_mod_cast (show 2 * k + 3 ≠ 0 by omega)
      have hne2 : ((k : K) + 1 - 3) ≠ 0 := by
        have e : ((k - 2 : ℕ) : K) = (k : K) + 1 - 3 := by
          push_cast [Nat.cast_sub (show 2 ≤ k by omega)]
          ring
        rw [← e]
        exact_mod_cast (show k - 2 ≠ 0 by omega)
      push_cast
      rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hne1 hne2)]
      linear_combination -hrec

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ k`. Rewrite using `[coeff_succ_X_mul, coeff_derivative]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_X_mul_derivative' {K : Type} [Field K] (f : K⟦X⟧) (n : ℕ) :
    coeff n (X * derivative K f) = (n : K) * coeff n f := by
  cases n with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

end BridgeK

open BridgeK Formalism.L2.Th1.CM in
/- English proof (translation)
Unfold `WpNumEq`. Introduce `K _ _ W`. Take `⟨_, h0, hodd, _, _⟩` from `hS K W`. Prove the components needed by the constructor for the conclusion. Use extensionality with `n`.

Unfold `wpNum`. Rewrite using `[coeff_mk, map_add, coeff_one, coeff_X_pow_mul']`. Take `⟨j, rfl | rfl⟩` from `Nat.even_or_odd' n`. Break down `Nat.lt_or_ge j 1 with hj | hj` into its components or cases. Use `interval_cases j`.

Simplify using the standard rewrite rules. Take `⟨i, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`. Rewrite using `[if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1)), if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (show 2 ≤ 2 * (i + 1) by omega), Nat.mul_div_cancel_left (i + 1) (by norm_num : 0 < 2), show 2 * (i + 1) - 2 = 2 * i by omega, cW_succ hS hR W i, zero_add]`. Rewrite using `[if_neg (show 2 * j + 1 ≠ 0 by omega), if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)), if_neg (show 2 * j + 1 ≠ 0 by omega), zero_add] split_ifs with h`. Rewrite using `[show 2 * j + 1 - 2 = 2 * (j - 1) + 1 by omega, hodd _ (odd_two_mul_add_one (j - 1))]`.

Both sides reduce to the same expression. Use extensionality with `n`. Unfold `wpDen`. Rewrite using `[coeff_mk, map_sub, coeff_one, mul_assoc (C (1 / 2 : K)) (X ^ 3) (derivative K (wpReg W)), coeff_C_mul, coeff_X_pow_mul']`. Take `⟨j, rfl | rfl⟩` from `Nat.even_or_odd' n`.

Break down `Nat.lt_or_ge j 2 with hj | hj` into its components or cases. Apply the tactic sequence `interval_cases j <;> simp`. Take `⟨i, rfl⟩ : ∃ i, j = i + 1 + 1` from `⟨j - 2, by omega⟩`. Rewrite using `[if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1 + 1)), if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (show 3 ≤ 2 * (i + 1 + 1) by omega), Nat.mul_div_cancel_left (i + 1 + 1) (by norm_num : 0 < 2), show 2 * (i + 1 + 1) - 3 = 2 * i + 1 by omega, coeff_ …`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (show 2 * j + 1 ≠ 0 by omega), if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)), if_neg (show 2 * j + 1 ≠ 0 by omega)] split_ifs with h`. Rewrite using `[show 2 * j + 1 - 3 = 2 * (j - 1) by omega, coeff_derivative, hodd _ (odd_two_mul_add_one (j - 1))]`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wpNumEq_of (hS : WpShape.{0}) (hR : WpRecursion.{0}) : WpNumEq := by
  unfold WpNumEq
  intro K _ _ W
  obtain ⟨_, h0, hodd, _, _⟩ := hS K W
  constructor
  · ext n
    unfold wpNum
    rw [coeff_mk, map_add, coeff_one, coeff_X_pow_mul']
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.lt_or_ge j 1 with hj | hj
      · interval_cases j
        simp
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1)),
          if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (show 2 ≤ 2 * (i + 1) by omega),
          Nat.mul_div_cancel_left (i + 1) (by norm_num : 0 < 2),
          show 2 * (i + 1) - 2 = 2 * i by omega, cW_succ hS hR W i, zero_add]
    · rw [if_neg (show 2 * j + 1 ≠ 0 by omega),
        if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)),
        if_neg (show 2 * j + 1 ≠ 0 by omega), zero_add]
      split_ifs with h
      · rw [show 2 * j + 1 - 2 = 2 * (j - 1) + 1 by omega, hodd _ (odd_two_mul_add_one (j - 1))]
      · rfl
  · ext n
    unfold wpDen
    rw [coeff_mk, map_sub, coeff_one, mul_assoc (C (1 / 2 : K)) (X ^ 3) (derivative K (wpReg W)),
      coeff_C_mul, coeff_X_pow_mul']
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · interval_cases j <;> simp
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + 1 := ⟨j - 2, by omega⟩
        rw [if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1 + 1)),
          if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (show 3 ≤ 2 * (i + 1 + 1) by omega),
          Nat.mul_div_cancel_left (i + 1 + 1) (by norm_num : 0 < 2),
          show 2 * (i + 1 + 1) - 3 = 2 * i + 1 by omega, coeff_derivative,
          show 2 * i + 1 + 1 = 2 * (i + 1) by ring, cW_succ hS hR W (i + 1)]
        push_cast
        ring
    · rw [if_neg (show 2 * j + 1 ≠ 0 by omega),
        if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)),
        if_neg (show 2 * j + 1 ≠ 0 by omega)]
      split_ifs with h
      · rw [show 2 * j + 1 - 3 = 2 * (j - 1) by omega, coeff_derivative,
          hodd _ (odd_two_mul_add_one (j - 1))]
        ring
      · ring

/- English proof (translation)
Unfold `WpRegInv`. Introduce `K _ _ W W' h2 h3`. Use extensionality with `n`. Take `⟨k, rfl | rfl⟩` from `Nat.even_or_odd' n`. Rewrite using `[← BridgeK.cW_succ hS hR W k, ← BridgeK.cW_succ hS hR W' k, h2, h3]`.

Rewrite using `[(hS K W).2.2.1 _ (odd_two_mul_add_one k), (hS K W').2.2.1 _ (odd_two_mul_add_one k)]`.
-/
theorem wpRegInv_of (hS : WpShape.{0}) (hR : WpRecursion.{0}) : WpRegInv := by
  unfold WpRegInv
  intro K _ _ W W' h2 h3
  ext n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [← BridgeK.cW_succ hS hR W k, ← BridgeK.cW_succ hS hR W' k, h2, h3]
  · rw [(hS K W).2.2.1 _ (odd_two_mul_add_one k), (hS K W').2.2.1 _ (odd_two_mul_add_one k)]

/- English proof (translation)
Introduce `K _ _ g2 g3`. Take `⟨hb, hg2, hg3, -⟩` from `short_weierstrass_inverse K g2 g3`. Use `set W := shortW g2 g3 with hW`. Take `⟨hnum, hden⟩` from `wpNumEq_of hS hR K W`. Rewrite `hnum`, `hden` using `[hg2, hg3]`.

Take `⟨hshape, -⟩` from `hS K W`. Take `⟨hd, -⟩` from `wpODE.{0} K W`. Take `⟨-, hfl⟩` from `flowZ.{0} K W`. Establish `hx : wpL W = xZ W`. Rewrite using `[wpL, hb]`.

Simplify using the standard rewrite rules. Establish `ha1 : W.a₁ = 0` using `rfl`. Establish `ha3 : W.a₃ = 0` using `rfl`. Rewrite `hd` using `[ha1, ha3, map_zero, zero_mul, add_zero, add_zero]`. Establish `hrel : toL (expSer W) * dL (wpL W) = -2 * wpL W`.

Rewrite using `[hd, hx]`. Take the linear combination `2 * hfl`. Rewrite `hrel` using `[hshape, map_add, dL_uPow, dL_toL]`. Establish `h3 : (uPow (-2 - 1) : LaurentSeries K) * toL (X ^ 3) = 1`. Rewrite using `[← uPow_natCast]`.

Conclude with `uPow_neg_mul 3`. Establish `h2 : (uPow (-2) : LaurentSeries K) * toL (X ^ 3) = toL X`. Rewrite using `[← uPow_natCast, ← uPow_add, ← uPow_one]`. Evaluate the numerical expressions. Establish `hC : (HahnSeries.C (((-2 : ℤ)) : K) : LaurentSeries K) = toL (C (-2 : K))`.

Rewrite using `[toL_C]`. Evaluate the numerical expressions. Establish `hps : expSer W * (C (-2 : K) + X ^ 3 * derivative K (wpReg W)) = C (-2 : K) * (X + X ^ 3 * wpReg W)`. Apply `toL_injective` to reduce the goal to its premises. Establish `hm2 : (toL (C (-2 : K)) : LaurentSeries K) = -2`.

Rewrite using `[map_neg C, map_neg toL]`. Use `congr 1`. Rewrite using `[map_ofNat C, map_ofNat toL]`. Simplify using `only [map_mul, map_add]`. Rewrite `hrel` using `[hC]`.

Take the linear combination `toL (X ^ 3) * hrel - toL (expSer W) * toL (C (-2 : K)) * h3 - 2 * h2 - (toL X + toL (X ^ 3) * toL (wpReg W)) * hm2`. Establish `hab : (C (1 / 2 : K) : K⟦X⟧) * C (-2 : K) = -1`. Rewrite using `[← map_mul]`. Evaluate the numerical expressions. Establish `hcc : constantCoeff (CM.wpDen g2 g3) ≠ 0`.

Rewrite using `[hden]`. Simplify using the standard rewrite rules. Use `symm`. Rewrite using `[CM.uSer, eq_mul_inv_iff_mul_eq hcc, hnum, hden]`. Take the linear combination `-(C (1 / 2 : K) : K⟦X⟧) * hps + (expSer W - X - X ^ 3 * wpReg W) * hab`.
-/
theorem uSerEq_of (hS : WpShape.{0}) (hR : WpRecursion.{0}) : USerEq := by
  intro K _ _ g2 g3
  obtain ⟨hb, hg2, hg3, -⟩ := short_weierstrass_inverse K g2 g3
  set W := shortW g2 g3 with hW
  obtain ⟨hnum, hden⟩ := wpNumEq_of hS hR K W
  rw [hg2, hg3] at hnum hden
  obtain ⟨hshape, -⟩ := hS K W
  obtain ⟨hd, -⟩ := wpODE.{0} K W
  obtain ⟨-, hfl⟩ := flowZ.{0} K W
  have hx : wpL W = xZ W := by
    rw [wpL, hb]; simp
  have ha1 : W.a₁ = 0 := rfl
  have ha3 : W.a₃ = 0 := rfl
  rw [ha1, ha3, map_zero, zero_mul, add_zero, add_zero] at hd

  have hrel : toL (expSer W) * dL (wpL W) = -2 * wpL W := by
    rw [hd, hx]; linear_combination 2 * hfl
  rw [hshape, map_add, dL_uPow, dL_toL] at hrel
  have h3 : (uPow (-2 - 1) : LaurentSeries K) * toL (X ^ 3) = 1 := by
    rw [← uPow_natCast]; exact uPow_neg_mul 3
  have h2 : (uPow (-2) : LaurentSeries K) * toL (X ^ 3) = toL X := by
    rw [← uPow_natCast, ← uPow_add, ← uPow_one]; norm_num
  have hC : (HahnSeries.C (((-2 : ℤ)) : K) : LaurentSeries K) = toL (C (-2 : K)) := by
    rw [toL_C]; norm_num
  have hps : expSer W * (C (-2 : K) + X ^ 3 * derivative K (wpReg W)) =
      C (-2 : K) * (X + X ^ 3 * wpReg W) := by
    apply toL_injective
    have hm2 : (toL (C (-2 : K)) : LaurentSeries K) = -2 := by
      rw [map_neg C, map_neg toL]; congr 1
      rw [map_ofNat C, map_ofNat toL]
    simp only [map_mul, map_add]
    rw [hC] at hrel
    linear_combination toL (X ^ 3) * hrel - toL (expSer W) * toL (C (-2 : K)) * h3 - 2 * h2
      - (toL X + toL (X ^ 3) * toL (wpReg W)) * hm2
  have hab : (C (1 / 2 : K) : K⟦X⟧) * C (-2 : K) = -1 := by
    rw [← map_mul]; norm_num
  have hcc : constantCoeff (CM.wpDen g2 g3) ≠ 0 := by
    rw [hden]; simp
  symm
  rw [CM.uSer, eq_mul_inv_iff_mul_eq hcc, hnum, hden]
  linear_combination -(C (1 / 2 : K) : K⟦X⟧) * hps + (expSer W - X - X ^ 3 * wpReg W) * hab

end Formalism.L2.Th1.A
