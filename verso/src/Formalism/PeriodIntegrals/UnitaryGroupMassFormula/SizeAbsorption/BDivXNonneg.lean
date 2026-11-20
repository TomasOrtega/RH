import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.Development

noncomputable section

namespace PI.SzEatI.W

open Formalism.BasicNotions Formalism.MainNotions.G

section basic

variable {D : D7} (L : SizeData₂ D)

/- English proof (translation)
The claim follows from `L.sc.one_lt_alt.le`.
-/
theorem x_one_le : 1 ≤ L.sc.x := L.sc.one_lt_alt.le

/- English proof (translation)
The claim follows from `lt_trans one_pos L.sc.one_lt_alt`.
-/
theorem x_pos : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt

/- English proof (translation)
The claim follows from `Real.exp_pos _`.
-/
theorem b_pos : 0 < L.sc.b := Real.exp_pos _

/- English proof (translation)
Unfold `Scale.b Scale.L`. Conclude with `Real.one_le_exp (Real.rpow_nonneg (x_pos L).le _)`.
-/
theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b Scale.L
  exact Real.one_le_exp (Real.rpow_nonneg (x_pos L).le _)

/- English proof (translation)
The claim follows from `mul_pos (x_pos L) (b_pos L)`.
-/
theorem a_pos : 0 < L.sc.a := mul_pos (x_pos L) (b_pos L)

/- English proof (translation)
The claim follows from `div_pos (a_pos L) (Real.exp_pos _)`.
-/
theorem b'_pos : 0 < L.sc.b' := div_pos (a_pos L) (Real.exp_pos _)

/- English proof (translation)
Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions.
-/
theorem n_one_le : (1 : ℝ) ≤ (D.R.n : ℝ) := by
  have : 1 ≤ D.R.n := D.R.ord_pos
  exact_mod_cast this

/- English proof (translation)
The claim follows from `div_nonneg (b'_pos L).le (mul_nonneg (x_pos L).le (Nat.cast_nonneg _))`.
-/
theorem w''_nonneg : 0 ≤ L.sc.w'' D.R.n :=
  div_nonneg (b'_pos L).le (mul_nonneg (x_pos L).le (Nat.cast_nonneg _))

/- English proof (translation)
The claim follows from `div_le_self (b'_pos L).le (one_le_mul_of_one_le_of_one_le (x_one_le L) (n_one_le (D := D)))`.
-/
theorem w''_le_b' : L.sc.w'' D.R.n ≤ L.sc.b' :=
  div_le_self (b'_pos L).le (one_le_mul_of_one_le_of_one_le (x_one_le L) (n_one_le (D := D)))

/- English proof (translation)
The claim follows from `div_le_self (b'_pos L).le (x_one_le L)`.
-/
theorem b'_div_x_le : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self (b'_pos L).le (x_one_le L)

/- English proof (translation)
The claim follows from `div_nonneg (b'_pos L).le (x_pos L).le`.
-/
theorem b'_div_x_nonneg : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (b'_pos L).le (x_pos L).le

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -⟩` from `hSz`. Establish `hx` using `x_pos L`. Establish `hLa0 : 0 ≤ L.LaG` using `le_trans (Real.rpow_nonneg hx.le _) hLa.1`. Use `set q := Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) with hq`. Establish `h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / (D.R.k : ℝ)` using `div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (x_one_le L))) hLa0) (Nat.cast_nonneg _)`.

Establish `h3 : L.sc.x ^ (-2 : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos (x_one_le L) (by norm_num)`. Establish `h4 : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) = 4 * q`. Rewrite using `[hq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hR` using `hRho`.

Unfold `Formalism.MainNotions.SizeRho at hR`. Rewrite `hR` using `[h4]`. Establish `hq1 : q ≤ 1` using `by linarith`. Establish `hB` using `hBot t`. Establish `h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) = q * L.sc.b'`.

Rewrite using `[hq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hB` using `[h5]`. Establish `h6 : q * L.sc.b' ≤ L.sc.b'` using `mul_le_of_le_one_left (b'_pos L).le hq1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bT_le (hSz : Formalism.MainNotions.SizesAt L) (t : D.host.TT) : (L.bT t : ℝ) ≤ 2 * L.sc.b' := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -⟩ := hSz
  have hx := x_pos L
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg hx.le _) hLa.1
  set q := Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) with hq
  have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / (D.R.k : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (x_one_le L))) hLa0)
      (Nat.cast_nonneg _)
  have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (x_one_le L) (by norm_num)
  have h4 : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) = 4 * q := by
    rw [hq]; ring
  have hR := hRho
  unfold Formalism.MainNotions.SizeRho at hR
  rw [h4] at hR
  have hq1 : q ≤ 1 := by linarith
  have hB := hBot t
  have h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) = q * L.sc.b' := by
    rw [hq]; ring
  rw [h5] at hB
  have h6 : q * L.sc.b' ≤ L.sc.b' := mul_le_of_le_one_left (b'_pos L).le hq1
  linarith

end basic

/- English proof (translation)
Introduce `D L hSz hbb j hj z`. Unfold `SizeData₂.lifts at hj`. Take `⟨hj1, hjm⟩` from `Finset.mem_Icc.1 hj`. Unfold `wPl`. Establish `hη` using `L.etaSz_pos`.

Establish `hb` using `b_pos L`. Distinguish the cases in `hth : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces`. Establish `hw` using `L.win_thick j hj1 hjm (tauPl D z) hth`. Apply the tactic sequence `constructor <;> linarith [hw.1, hw.2]`. Distinguish the cases in `htop : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces`.

Take `⟨t, ht, hte⟩` from `Finset.mem_image.1 htop`. Establish `hw` using `L.win_top j hj1 hjm (tauPl D z) ⟨t, ht⟩ hte.symm`. Establish `hbt` using `bT_le L hSz ⟨t, ht⟩`. Establish `hbt0` using `L.bT_ge ⟨t, ht⟩`. Establish `h1` using `b'_div_x_le L`.

Establish `h2` using `b'_div_x_nonneg L`. Establish `h3` using `(b'_pos L).le`. Apply the tactic sequence `constructor <;> linarith [hw.1, hw.2]`. Establish `hthin : D.host.IsThin (D.eTau (tauPl D z) : D.R.GG)` using `⟨(D.eTau (tauPl D z)).2, htop, hth⟩`. Establish `hw` using `L.win_thin j hj1 hjm (tauPl D z) hthin`.

Establish `h1` using `w''_nonneg L`. Establish `h2` using `w''_le_b' L`. Apply the tactic sequence `constructor <;> linarith [hw.1, hw.2]`.
-/
theorem stepW : StepW := by
  intro D L hSz hbb j hj z
  unfold SizeData₂.lifts at hj
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
  unfold wPl
  have hη := L.etaSz_pos
  have hb := b_pos L
  by_cases hth : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
  · have hw := L.win_thick j hj1 hjm (tauPl D z) hth
    constructor <;> linarith [hw.1, hw.2]
  by_cases htop : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
    have hw := L.win_top j hj1 hjm (tauPl D z) ⟨t, ht⟩ hte.symm
    have hbt := bT_le L hSz ⟨t, ht⟩
    have hbt0 := L.bT_ge ⟨t, ht⟩
    have h1 := b'_div_x_le L
    have h2 := b'_div_x_nonneg L
    have h3 := (b'_pos L).le
    constructor <;> linarith [hw.1, hw.2]
  · have hthin : D.host.IsThin (D.eTau (tauPl D z) : D.R.GG) := ⟨(D.eTau (tauPl D z)).2, htop, hth⟩
    have hw := L.win_thin j hj1 hjm (tauPl D z) hthin
    have h1 := w''_nonneg L
    have h2 := w''_le_b' L
    constructor <;> linarith [hw.1, hw.2]

end PI.SzEatI.W
