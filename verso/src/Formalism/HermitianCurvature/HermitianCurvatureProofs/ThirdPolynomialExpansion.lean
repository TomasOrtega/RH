import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3

/- English proof (translation)
Unfold `Fin.succAbove`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def] <;> omega`.
-/
theorem succAbove_val {n : ℕ} (p : Fin (n + 1)) (l : Fin n) :
    (p.succAbove l).val = if l.val < p.val then l.val else l.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def] <;> omega

/- English proof (translation)
Unfold `sgnW`. Rewrite using `[← pow_add]`. Use `congr 1`. Consider the cases of `s with`. Consider the case `zero => rfl`.

Consider the case `succ k`. Establish `e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1)`. Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero`. Establish `hs : sgnW 0 = 1` using `by simp [sgnW]`. Rewrite using `[hs, pow_zero, mul_one, mul_one]`. Use `show Matrix.det (Matrix.of fun a b : Fin i0 => Zb i0 0 h t a.val b.val) = _`.

Use `congr 1`. Use extensionality with `a b`. Simplify using `[Zb, a.isLt, b.isLt]`. Consider the case `succ s ih`. Rewrite using `[Matrix.det_succ_row _ (⟨i0, by omega⟩ : Fin (i0 + s + 1)), Finset.sum_eq_single (Fin.last _)]`.

Establish `hsub : (Matrix.of fun a b : Fin (i0 + (s + 1)) => Zb i0 (s + 1) h t a.val b.val).submatrix (⟨i0, by omega⟩ : Fin (i0 + s + 1)).succAbove (Fin.last (i0 + s)).succAbove = Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply, succAbove_val, Fin.succAbove_last, Fin.coe_castSucc]`. Establish `hb` using `b.isLt`. Distinguish the cases in `ha : (a : ℕ) < i0`.

Simplify using `only [ha, if_true]`. Unfold `Zb`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Simplify using `only [ha, if_false]`. Unfold `Zb`.

Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Rewrite using `[hsub, ih, sgnW_succ']`. Establish `he : Zb i0 (s + 1) h t i0 (i0 + s) = t`. Simplify using `only [Zb]`. Rewrite using `[dif_neg (lt_irrefl _), if_pos (by omega)]`.

Simplify using `only [Matrix.of_apply, Fin.val_last]`. Rewrite using `[he]`. Rewrite using `[show i0 + (i0 + s) = 2 * i0 + s by ring, pow_add, pow_mul]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.

Introduce `j _ hj`. Establish `hj' : (j : ℕ) ≠ i0 + s` using `fun e => hj (Fin.ext (by simp [e]))`. Establish `he : Zb i0 (s + 1) h t i0 j = 0`. Use `j.isLt` as an intermediate fact. Simplify using `only [Zb]`.

Rewrite using `[dif_neg (lt_irrefl _), if_neg (by omega)]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[he, mul_zero, zero_mul]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`.
-/
theorem zb_det (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) :
    (Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val).det = h.det * t ^ s * sgnW s := by
  induction s with
  | zero =>
    have hs : sgnW 0 = 1 := by simp [sgnW]
    rw [hs, pow_zero, mul_one, mul_one]
    show Matrix.det (Matrix.of fun a b : Fin i0 => Zb i0 0 h t a.val b.val) = _
    congr 1
    ext a b
    simp [Zb, a.isLt, b.isLt]
  | succ s ih =>
    rw [Matrix.det_succ_row _ (⟨i0, by omega⟩ : Fin (i0 + s + 1)), Finset.sum_eq_single (Fin.last _)]
    · have hsub : (Matrix.of fun a b : Fin (i0 + (s + 1)) => Zb i0 (s + 1) h t a.val b.val).submatrix
          (⟨i0, by omega⟩ : Fin (i0 + s + 1)).succAbove (Fin.last (i0 + s)).succAbove =
          Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, succAbove_val, Fin.succAbove_last,
          Fin.coe_castSucc]
        have hb := b.isLt
        by_cases ha : (a : ℕ) < i0
        · simp only [ha, if_true]
          unfold Zb
          split_ifs <;> first | rfl | omega
        · simp only [ha, if_false]
          unfold Zb
          split_ifs <;> first | rfl | omega
      rw [hsub, ih, sgnW_succ']
      have he : Zb i0 (s + 1) h t i0 (i0 + s) = t := by
        simp only [Zb]
        rw [dif_neg (lt_irrefl _), if_pos (by omega)]
      simp only [Matrix.of_apply, Fin.val_last]
      rw [he]
      rw [show i0 + (i0 + s) = 2 * i0 + s by ring, pow_add, pow_mul]
      norm_num
      ring
    · intro j _ hj
      have hj' : (j : ℕ) ≠ i0 + s := fun e => hj (Fin.ext (by simp [e]))
      have he : Zb i0 (s + 1) h t i0 j = 0 := by
        have := j.isLt
        simp only [Zb]
        rw [dif_neg (lt_irrefl _), if_neg (by omega)]
      simp only [Matrix.of_apply]
      rw [he, mul_zero, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

/- English proof (translation)
Introduce `i0 s h t`. Use `⟨?_, zb_det i0 s h t⟩` and prove the remaining obligations. Unfold `Dlead`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `[Zb, a.isLt, b.isLt]`.
-/
theorem derivative_leading_zb : DleadZb := by
  intro i0 s h t
  refine ⟨?_, zb_det i0 s h t⟩
  unfold Dlead
  congr 1
  ext a b
  simp [Zb, a.isLt, b.isLt]

/- English proof (translation)
Introduce `i0 s' h t c`. Distinguish the cases in `hc : c.val = i0`. Rewrite using `[if_pos hc, ← zb_det i0 s' h t]`. Use `congr 1`. Use extensionality with `a l`.

Simplify using `only [Matrix.of_apply, succAbove_val, hc]`. Establish `hl` using `l.isLt`. Distinguish the cases in `hl0 : (l : ℕ) < i0`. Simplify using `only [hl0, if_true]`. Unfold `Zb`.

Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Simplify using `only [hl0, if_false]`. Unfold `Zb`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Rewrite using `[if_neg hc]`.

Establish `hne : (⟨i0, by omega⟩ : Fin (i0 + s' + 1)) ≠ c` using `fun e => hc (by rw [← e])`. Take `⟨l0, hl0⟩` from `Fin.exists_succAbove_eq hne`. Apply `Matrix.det_eq_zero_of_column_eq_zero l0` to reduce the goal to its premises. Introduce `a`. Simplify using `only [Matrix.of_apply, hl0]`.

Establish `ha` using `a.isLt`. Unfold `Zb`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem minors_first_case : MinorsFirstCase := by
  intro i0 s' h t c
  by_cases hc : c.val = i0
  · rw [if_pos hc, ← zb_det i0 s' h t]
    congr 1
    ext a l
    simp only [Matrix.of_apply, succAbove_val, hc]
    have hl := l.isLt
    by_cases hl0 : (l : ℕ) < i0
    · simp only [hl0, if_true]
      unfold Zb
      split_ifs <;> first | rfl | omega
    · simp only [hl0, if_false]
      unfold Zb
      split_ifs <;> first | rfl | omega
  · rw [if_neg hc]
    have hne : (⟨i0, by omega⟩ : Fin (i0 + s' + 1)) ≠ c := fun e => hc (by rw [← e])
    obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hne
    apply Matrix.det_eq_zero_of_column_eq_zero l0
    intro a
    simp only [Matrix.of_apply, hl0]
    have ha := a.isLt
    unfold Zb
    split_ifs <;> first | rfl | omega

/- English proof (translation)
Introduce `i0 s'' h t`. Rewrite using `[← zb_det i0 s'' h t]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, succAbove_val]`.

Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Apply the tactic sequence `by_cases ha0 : (a : ℕ) < i0 <;> by_cases hb0 : (b : ℕ) < i0 <;>`. Apply the tactic sequence `simp only [ha0, hb0, if_true, if_false] <;>`. Apply the tactic sequence `unfold Zb <;> split_ifs <;> first | rfl | omega`.
-/
theorem third_polynomial_expansion : MinorsThirdCase := by
  intro i0 s'' h t
  rw [← zb_det i0 s'' h t]
  congr 1
  ext a b
  simp only [Matrix.of_apply, succAbove_val]
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha0 : (a : ℕ) < i0 <;> by_cases hb0 : (b : ℕ) < i0 <;>
    simp only [ha0, hb0, if_true, if_false] <;>
    unfold Zb <;> split_ifs <;> first | rfl | omega

end Formalism.FourierDecayAlt.P.SignAntidiagonal
