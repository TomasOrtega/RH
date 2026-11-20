import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Development

noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

/- English proof (translation)
Introduce `D L hSz hx`. Take `⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, hEta, -, -, hDel, -⟩` from `hSz`. Establish `hx0 : (0 : ℝ) < L.sc.x` using `by linarith`. Establish `hx1 : (1 : ℝ) ≤ L.sc.x` using `by linarith`. Establish `hb1 : 1 ≤ L.sc.b`.

Unfold `Scale.b`. Conclude with `Real.one_le_exp (Real.rpow_nonneg hx0.le _)`. Establish `hb'0 : 0 ≤ L.sc.b'`. Unfold `Scale.b' Scale.a`. Conclude with `div_nonneg (mul_nonneg hx0.le (by linarith)) (Real.exp_pos _).le`.

Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Unfold `Formalism.BasicNotions.Ranks.n`. Conclude with `D.R.ord_pos` after adjusting the coercions. Establish `ht1 : (1 : ℝ) ≤ D.R.t` using `by exact_mod_cast D.R.t_odd.pos`. Establish `hη` using `L.etaSz_pos`.

Use `⟨?_, ?_, hDel.2.2.2.1, ?_, hEta.2.2.2.2.1, hb1, hb'0⟩` and prove the remaining obligations. Introduce `t`. Establish `hLa0 : 0 ≤ L.LaG` using `le_trans (Real.rpow_nonneg hx0.le _) hLa.1`. Establish `hk0 : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Use `set Q := Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k with hQ`.

Establish `h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k` using `div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_nonneg hx1)) hLa0) hk0`. Establish `h3 : L.sc.x ^ (-2 : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)`. Establish `h4 : 4 * Q ≤ 1`. Establish `: 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * Q` using `by rw [hQ]; ring`. Unfold `Formalism.MainNotions.SizeRho at hRho`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5` using `hBot t`. Establish `h6 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = Q * L.sc.b'`. Rewrite using `[hQ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h5` using `[h6]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h` using `hEta.2.2.2.1`. Combine the equalities or inequalities in the displayed calculation. Unfold `Scale.w''`.

Conclude with `div_le_div_of_nonneg_left hb'0 hx0 (le_mul_of_one_le_right hx0.le hn1)`.
-/
theorem sizeFacts : SizeFacts := by
  intro D L hSz hx
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, hEta, -, -, hDel, -⟩ := hSz
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have hx1 : (1 : ℝ) ≤ L.sc.x := by linarith
  have hb1 : 1 ≤ L.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hb'0 : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a
    exact div_nonneg (mul_nonneg hx0.le (by linarith)) (Real.exp_pos _).le
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    unfold Formalism.BasicNotions.Ranks.n; exact_mod_cast D.R.ord_pos
  have ht1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have hη := L.etaSz_pos
  refine ⟨?_, ?_, hDel.2.2.2.1, ?_, hEta.2.2.2.2.1, hb1, hb'0⟩
  · intro t
    have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg hx0.le _) hLa.1
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    set Q := Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k with hQ
    have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
      div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_nonneg hx1)) hLa0) hk0
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have h4 : 4 * Q ≤ 1 := by
      have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * Q := by rw [hQ]; ring
      unfold Formalism.MainNotions.SizeRho at hRho
      linarith
    have h5 := hBot t
    have h6 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = Q * L.sc.b' := by
      rw [hQ]; ring
    rw [h6] at h5
    nlinarith
  · have h := hEta.2.2.2.1
    calc L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := le_mul_of_one_le_left hη.le ht1
      _ ≤ _ := h
  · unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'0 hx0 (le_mul_of_one_le_right hx0.le hn1)

end PI.SzCt.UnitaryGroupMassFormula
