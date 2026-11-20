import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaFactorisation

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

open Classical

section real

/- English proof (translation)
The claim follows from `|∏ t ∈ s, (y + lam t)| ≤ (1 + 3 / (β - α)) ^ s.card * |∏ t ∈ s, (y + 1 + lam t)| := by rw [Finset.abs_prod, Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib] refine Finset.prod_le_prod (fun t _ => abs_nonneg _) fun t ht => ?_ have hI0 : 0 < β - α := by linarith hav …`.
-/
theorem pratio (s : Finset ℕ) (lam : ℕ → ℝ) (α β y : ℝ) (hI : 3 ≤ β - α)
    (hroot : ∀ t ∈ s, -lam t < α ∨ β < -lam t) (hy1 : α + (β - α) / 3 ≤ y) (hy2 : y + 1 ≤ β - (β - α) / 3) :
    |∏ t ∈ s, (y + lam t)| ≤ (1 + 3 / (β - α)) ^ s.card * |∏ t ∈ s, (y + 1 + lam t)| := by
  rw [Finset.abs_prod, Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun t _ => abs_nonneg _) fun t ht => ?_
  have hI0 : 0 < β - α := by linarith
  have h3 : 0 ≤ 3 / (β - α) := by positivity
  rcases hroot t ht with h | h
  · have a1 : 0 < y + lam t := by linarith
    rw [abs_of_pos a1, abs_of_pos (by linarith : 0 < y + 1 + lam t)]
    nlinarith
  · have a2 : y + 1 + lam t < 0 := by linarith
    have hd : (β - α) / 3 ≤ -(y + 1 + lam t) := by linarith
    rw [abs_of_neg (by linarith : y + lam t < 0), abs_of_neg a2]
    have : 1 ≤ 3 / (β - α) * -(y + 1 + lam t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI0]; linarith
    nlinarith

/- English proof (translation)
Establish `hb : 0 ≤ k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3` using `by positivity`. Establish `h1 : k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 ≤ I` using `by nlinarith`. Establish `h2 : 6 * k ≤ k * N * (r + 1) ^ 2`. Establish `: 20 ≤ N * (r + 1) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h3 : 6 * (2 * r + 1) ≤ N ^ 2 * (r + 1) ^ 2`. Establish `: 400 ≤ N ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : 0 ≤ N ^ 3` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem long_bound (k r N Cc I : ℝ) (hk : 1 ≤ k) (hr : 0 ≤ r) (hN : 20 ≤ N) (hCc : 1 ≤ Cc)
    (h : Cc * (k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ I) : 6 * (k + 2 * r + 1) ≤ I := by
  have hb : 0 ≤ k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 := by positivity
  have h1 : k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 ≤ I := by nlinarith
  have h2 : 6 * k ≤ k * N * (r + 1) ^ 2 := by
    have : 20 ≤ N * (r + 1) ^ 2 := by nlinarith
    nlinarith
  have h3 : 6 * (2 * r + 1) ≤ N ^ 2 * (r + 1) ^ 2 := by
    have : 400 ≤ N ^ 2 := by nlinarith
    nlinarith
  have h4 : 0 ≤ N ^ 3 := by positivity
  linarith

/- English proof (translation)
Establish `: 0 ≤ 6 * N ^ 3` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem three_le_len (N I : ℝ) (hN : 20 ≤ N) (h : 6 * N ^ 3 + 6 * N ≤ I) : 3 ≤ I := by
  have : 0 ≤ 6 * N ^ 3 := by positivity
  linarith

/- English proof (translation)
Establish `hpos : 0 < N ^ 2 - 1` using `by nlinarith`. Use `⟨hpos, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_ofNat, mul_div_assoc', div_le_iff₀ hpos]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_N_bound (N : ℝ) (hN : 20 ≤ N) : 0 < N ^ 2 - 1 ∧ ((2 : ℕ) : ℝ) * (N / (N ^ 2 - 1)) ≤ 1 / 2 := by
  have hpos : 0 < N ^ 2 - 1 := by nlinarith
  refine ⟨hpos, ?_⟩
  rw [Nat.cast_ofNat, mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

/- English proof (translation)
Establish `hsq : (√TT)⁻¹ ^ 2 = TT⁻¹` using `by rw [inv_pow, Real.sq_sqrt hTT.le]`. Establish `hsq0 : 0 < (√TT)⁻¹` using `inv_pos.2 (Real.sqrt_pos.2 hTT)`. Establish `hmain : Pa * (x0 * F) ≤ E1 * sA * (√TT)⁻¹ * q`. Establish `hl0 : 0 ≤ Pa * (x0 * F)` using `mul_nonneg hPa (mul_pos hx0 hF0).le`. Establish `hr0 : 0 ≤ E1 * sA * (√TT)⁻¹ * q` using `mul_nonneg (mul_nonneg (mul_nonneg hE1.le hsA) hsq0.le) hq.le`.

Rewrite using `[← pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero]`. Establish `eL : (Pa * (x0 * F)) ^ 2 = Pa ^ 2 * x0 ^ 2 * F ^ 2` using `by ring`. Establish `eR : (E1 * sA * (√TT)⁻¹ * q) ^ 2 = E1 * (sA ^ 2 * q) * (q / TT) * E1`. Rewrite using `[mul_pow, mul_pow, mul_pow, hsq]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[eL, eR]`. Establish `hx2 : 0 ≤ x0 ^ 2` using `sq_nonneg _`. Establish `hF2 : 0 ≤ F ^ 2` using `sq_nonneg _`. Establish `hA : 0 ≤ E1 * (sA ^ 2 * q)` using `by positivity`. Establish `hB : 0 ≤ q / TT` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Establish `hC : Real.exp 1 * sA * (√TT)⁻¹ * (E1⁻¹ * q) = E1 * sA * (√TT)⁻¹ * q`. Rewrite using `[← hE1sq]`. Clear the denominators using the available nonvanishing facts. Establish `hfin : Pa * (x0 * F) ≤ Real.exp 1 * sA * (√TT)⁻¹ * qw`.

Rewrite `hmain` using `[← hC]`. Use `hmain.trans (mul_le_mul_of_nonneg_left hqw ?_)` and prove the remaining obligations. Check the signs of the components of the expression. Rewrite using `[← mul_div_assoc, le_div_iff₀ (mul_pos hx0 hF0)]`. Conclude with `hfin`.
-/
theorem final_cmp (Pa x0 F q TT sA E1 qw : ℝ) (hPa : 0 ≤ Pa) (hx0 : 0 < x0) (hF0 : 0 < F) (hq : 0 < q) (hTT : 0 < TT)
    (hsA : 0 ≤ sA) (hE1 : 0 < E1) (hE1sq : E1 ^ 2 = Real.exp 1) (hP2 : Pa ^ 2 ≤ E1 * (sA ^ 2 * q))
    (hx : x0 ^ 2 ≤ q / TT) (hF : F ^ 2 ≤ E1) (hqw : E1⁻¹ * q ≤ qw) :
    Pa ≤ Real.exp 1 * sA * (√TT)⁻¹ * (qw / (x0 * F)) := by
  have hsq : (√TT)⁻¹ ^ 2 = TT⁻¹ := by rw [inv_pow, Real.sq_sqrt hTT.le]
  have hsq0 : 0 < (√TT)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hTT)
  have hmain : Pa * (x0 * F) ≤ E1 * sA * (√TT)⁻¹ * q := by
    have hl0 : 0 ≤ Pa * (x0 * F) := mul_nonneg hPa (mul_pos hx0 hF0).le
    have hr0 : 0 ≤ E1 * sA * (√TT)⁻¹ * q := mul_nonneg (mul_nonneg (mul_nonneg hE1.le hsA) hsq0.le) hq.le
    rw [← pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero]
    have eL : (Pa * (x0 * F)) ^ 2 = Pa ^ 2 * x0 ^ 2 * F ^ 2 := by ring
    have eR : (E1 * sA * (√TT)⁻¹ * q) ^ 2 = E1 * (sA ^ 2 * q) * (q / TT) * E1 := by
      rw [mul_pow, mul_pow, mul_pow, hsq]; field_simp
    rw [eL, eR]
    have hx2 : 0 ≤ x0 ^ 2 := sq_nonneg _
    have hF2 : 0 ≤ F ^ 2 := sq_nonneg _
    have hA : 0 ≤ E1 * (sA ^ 2 * q) := by positivity
    have hB : 0 ≤ q / TT := by positivity
    calc Pa ^ 2 * x0 ^ 2 * F ^ 2 ≤ E1 * (sA ^ 2 * q) * x0 ^ 2 * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * E1 := by gcongr
  have hC : Real.exp 1 * sA * (√TT)⁻¹ * (E1⁻¹ * q) = E1 * sA * (√TT)⁻¹ * q := by
    rw [← hE1sq]; field_simp
  have hfin : Pa * (x0 * F) ≤ Real.exp 1 * sA * (√TT)⁻¹ * qw := by
    rw [← hC] at hmain
    refine hmain.trans (mul_le_mul_of_nonneg_left hqw ?_)
    positivity
  rw [← mul_div_assoc, le_div_iff₀ (mul_pos hx0 hF0)]
  exact hfin

/- English proof (translation)
Rewrite using `[Real.exp_nat_mul]`. Conclude with `pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n`.
-/
theorem one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (1 + x) ^ n ≤ Real.exp (n * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n

end real

section xs

/- English proof (translation)
The claim follows from `| [], _, _ => by simp [Fr.xs] | l :: L, e, Y => by simp only [Fr.xs, List.map_cons, List.prod_cons] rw [xs_eq_prod x0 L e Y] ring`.
-/
theorem xs_eq_prod {S : Type} [Fintype S] [DecidableEq S] (x0 : ℂ → ℂ) :
    ∀ (L : List (Wd.Letter ℂ S)) (e : Wd.Ix S) (Y : ℂ),
      Fr.xs x0 L e Y = x0 Y * (L.map fun l => if e l.intersection_update_fsHerm_neg_one = 0 then Fr.phiL l Y else 1).prod
  | [], _, _ => by simp [Fr.xs]
  | l :: L, e, Y => by
    simp only [Fr.xs, List.map_cons, List.prod_cons]
    rw [xs_eq_prod x0 L e Y]
    ring

/- English proof (translation)
Establish `hD0 : 0 < D` using `by linarith`. Consider the cases of `b`. Simplify using `only [Bool.false_eq_true, if_false]`. Break down `le_or_gt 0 (y - pt) with h | h` into its components or cases. Rewrite `hd` using `[abs_of_nonneg h]`.

Establish `h1 : pt - y - 2 < 0` using `by linarith`. Establish `h2 : pt - y - 1 < 0` using `by linarith`. Prove the components needed by the constructor for the conclusion. Conclude with `div_pos_of_neg_of_neg h2 h1`. Rewrite using `[div_le_iff_of_neg h1]`.

Establish `: 0 < 1 / D` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Rewrite `hd` using `[abs_of_neg h]`. Establish `h1 : 0 < pt - y - 2` using `by linarith`. Prove the components needed by the constructor for the conclusion.

Conclude with `div_pos (by linarith) h1`. Rewrite using `[div_le_iff₀ h1]`. Establish `e1 : (1 + 1 / D) * (pt - y - 2) = pt - y - 2 + (pt - y - 2) / D` using `by ring`. Rewrite using `[e1]`. Establish `: 1 ≤ (pt - y - 2) / D` using `by rw [le_div_iff₀ hD0]; linarith`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [if_true]`. Break down `le_or_gt 0 (y - pt) with h | h` into its components or cases. Rewrite `hd` using `[abs_of_nonneg h]`. Establish `h1 : 0 < y - pt` using `by linarith`.

Prove the components needed by the constructor for the conclusion. Conclude with `div_pos (by linarith) h1`. Rewrite using `[div_le_iff₀ h1]`. Establish `e1 : (1 + 1 / D) * (y - pt) = y - pt + (y - pt) / D` using `by ring`. Rewrite using `[e1]`.

Establish `: 1 ≤ (y - pt) / D` using `by rw [le_div_iff₀ hD0]; linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hd` using `[abs_of_neg h]`. Establish `h2 : y + 1 - pt < 0` using `by linarith`. Prove the components needed by the constructor for the conclusion.

Conclude with `div_pos_of_neg_of_neg h2 h`. Rewrite using `[div_le_iff_of_neg h]`. Establish `: 0 < 1 / D` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem phiL_bound (b : Bool) (pt y D : ℝ) (hD : 2 ≤ D) (hd : D + 2 ≤ |y - pt|) :
    0 < (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ∧
      (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ≤ 1 + 1 / D := by
  have hD0 : 0 < D := by linarith
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : pt - y - 2 < 0 := by linarith
      have h2 : pt - y - 1 < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h1
      · rw [div_le_iff_of_neg h1]
        have : 0 < 1 / D := by positivity
        nlinarith
    · rw [abs_of_neg h] at hd
      have h1 : 0 < pt - y - 2 := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (pt - y - 2) = pt - y - 2 + (pt - y - 2) / D := by ring
        rw [e1]
        have : 1 ≤ (pt - y - 2) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
  · simp only [if_true]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : 0 < y - pt := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (y - pt) = y - pt + (y - pt) / D := by ring
        rw [e1]
        have : 1 ≤ (y - pt) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
    · rw [abs_of_neg h] at hd
      have h2 : y + 1 - pt < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h
      · rw [div_le_iff_of_neg h]
        have : 0 < 1 / D := by positivity
        nlinarith

end xs

end

end Formalism.FourierDecayAlt.P.PBL
