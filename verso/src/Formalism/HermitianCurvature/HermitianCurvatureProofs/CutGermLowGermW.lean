import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis

namespace Formalism.FourierDecayAlt.P.CutBP.GLG

open Formalism.FourierDecayAlt

noncomputable section

/- English proof (translation)
Substitute `he` using the available equality. Rewrite using `[show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul']`.
-/
theorem zpow_two_nat (x : ℝ) (e : ℤ) (n : ℕ) (he : e = 2 * (n : ℤ)) : x ^ e = (x ^ n) ^ 2 := by
  subst he
  rw [show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul']

/- English proof (translation)
Establish `e : h ++ [(m + 1, t), (1, c)] = (h ++ [(m + 1, t)]) ++ [(1, c)]` using `by simp`. Establish `hs1 : D.ptSize (h ++ [(m + 1, t)]) = b - 1 + (m + 1)`. Simplify using `only [D.ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hh ⊢`. Use linear arithmetic over natural numbers and integers. Unfold `TBB.nPt`.

Rewrite using `[e, PBD.weight_product_append, PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hs1, hh]`. Simplify using `only [C.nAux, one_mul, mul_one]`. Rewrite using `[if_neg (by omega), if_neg (by omega), mul_assoc]`. Use `congr 2`. Apply `zpow_two_nat` to reduce the goal to its premises.

Unfold `C.Mlev U.Mlev`. Establish `e1 : 1 + (b - 1) + (m + 1) - 1 = b + m` using `by omega`. Rewrite using `[e1]`. Move the coercions through the operations in `[Nat.cast_sub (show b + (m + 2) - 1 ≤ P.r from hi), Nat.cast_sub (show b + m ≤ P.r + 1 by omega)]`. Rewrite using `[Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Apply `zpow_two_nat` to reduce the goal to its premises. Unfold `C.Mlev U.Mlev`. Establish `e1 : 1 + (b - 1 + (m + 1)) + 1 - 1 = b + (m + 2) - 1` using `by omega`.

Rewrite using `[e1]`. Establish `h3 : 2 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3` using `by omega`. Move the coercions through the operations in `[Nat.cast_sub h3, Nat.cast_sub hi]`. Rewrite using `[Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nPt_block {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (t c : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 1, t), (1, c)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h *
        ((‖t‖ ^ ((m + 1) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m))) ^ 2 *
          (‖c‖ ^ (U.Mlev P.k (P.r - (b + (m + 2) - 1)) - 2)) ^ 2) := by
  have e : h ++ [(m + 1, t), (1, c)] = (h ++ [(m + 1, t)]) ++ [(1, c)] := by simp
  have hs1 : D.ptSize (h ++ [(m + 1, t)]) = b - 1 + (m + 1) := by
    simp only [D.ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hh ⊢
    omega
  unfold TBB.nPt
  rw [e, PBD.weight_product_append, PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hs1, hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega), if_neg (by omega), mul_assoc]
  congr 2
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1) + (m + 1) - 1 = b + m := by omega
    rw [e1]
    push_cast [Nat.cast_sub (show b + (m + 2) - 1 ≤ P.r from hi), Nat.cast_sub (show b + m ≤ P.r + 1 by omega)]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1 + (m + 1)) + 1 - 1 = b + (m + 2) - 1 := by omega
    rw [e1]
    have h3 : 2 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 := by omega
    push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring

/- English proof (translation)
Unfold `TBB.nPt`. Rewrite using `[PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hh]`. Simplify using `only [C.nAux, one_mul, mul_one]`. Rewrite using `[if_neg (by omega)]`. Use `congr 1`.

Apply `zpow_two_nat` to reduce the goal to its premises. Unfold `C.Mlev U.Mlev`. Establish `e1 : 1 + (b - 1) + (m + 2) - 1 = b + (m + 2) - 1` using `by omega`. Rewrite using `[e1]`. Establish `h3 : 1 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 + m` using `by omega`.

Move the coercions through the operations in `[Nat.cast_sub h3, Nat.cast_sub hi]`. Rewrite using `[Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nPt_long {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (z : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 2, z)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h * (‖z‖ ^ ((m + 2) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m - 1))) ^ 2 := by
  unfold TBB.nPt
  rw [PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega)]
  congr 1
  apply zpow_two_nat
  unfold C.Mlev U.Mlev
  have e1 : 1 + (b - 1) + (m + 2) - 1 = b + (m + 2) - 1 := by omega
  rw [e1]
  have h3 : 1 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 + m := by omega
  push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
  rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutBP.GLG
